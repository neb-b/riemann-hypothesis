module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2741
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDivisibleInLattice
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_divisible_in_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) → z = 0 := by
  first | (exact @GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat) | (exact GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat) | (intros; apply GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeAbsFrobeniusApplyF
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem isTr_absFrob_F : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type)
    [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt) (l l' : Mod B G h),
    IsTr B (frobRing (p_eq_zero p k)) h h (absFrob (p_eq_zero p k) G) l l' →
      ∀ y, l' (B.F G.dual (dual_conn h) y) = p * WittVector.frobenius (l y) := by
  intro p _ B k _ _ _ G h l l' hT y
  set hp := p_eq_zero p k
  letI : Algebra k k := (frobRing hp).toAlgebra
  obtain ⟨hb, lb, h1, h2⟩ := hT
  have hd := dual_conn h

  have eV : (PerfdLat.dualBaseChange k G).inv ≫ dualHom G (G.baseChange k)
      (absFrob hp G).lift = verschiebung hp G.dual := by
    have := dualHom_relFrob hp G
    change (frobTwistDual hp G).inv ≫ dualHom G _ (relFrob hp G) = _
    rw [← this, Iso.inv_hom_id_assoc]

  have eF : B.F G.dual hd y = B.map hd hb (relFrob hp G.dual)
      (B.smap hb hd (G.dual.toBase k) y) := by
    change B.smap hd hd (absFrob hp G.dual) y = B.smap hd hb (SemiHom.ofHom (relFrob hp G.dual))
      (B.smap hb hd (frobProj hp G.dual) y)
    exact B.smap_comp hd hb hd (frobProj hp G.dual) (SemiHom.ofHom (relFrob hp G.dual))
      (absFrob hp G.dual) (fun n a => by
        change (absFrob hp G.dual).app n a = (relFrob hp G.dual).app n ((frobProj hp G.dual).app n a)
        exact ((relFrob_app_frobProj hp n a).trans (absFrob_app hp G.dual n a).symm).symm) y
  have P := base_functor_props p _ B k (frobTwist hp G.dual) G.dual (frobTwist hp G.dual) hb hd hb
  have P' := base_functor_props p _ B k (frobTwist hp G.dual) (frobTwist hp G.dual)
    (frobTwist hp G.dual) hb hb hb
  have ep : B.map hb hd (verschiebung hp G.dual) (B.map hd hb (relFrob hp G.dual)
      (B.smap hb hd (G.dual.toBase k) y)) = p ^ 1 • B.smap hb hd (G.dual.toBase k) y := by
    set x := B.smap hb hd (G.dual.toBase k) y
    have c := P.2.1 (verschiebung hp G.dual) (relFrob hp G.dual)
    rw [verschiebung_comp_relFrob] at c
    have c2 := LinearMap.congr_fun c x
    calc B.map hb hd (verschiebung hp G.dual) (B.map hd hb (relFrob hp G.dual) x)
        = B.map hb hb ((p : ℤ_[p]) • 𝟙 _) x := c2.symm
      _ = p ^ 1 • B.map hb hb (𝟙 (frobTwist hp G.dual)) x := by
          have e := P'.2.2.2.2.1 1 (𝟙 (frobTwist hp G.dual)) x
          simp only [pow_one] at e ⊢
          exact e
      _ = p ^ 1 • x := congrArg _ (LinearMap.congr_fun P'.1 x)
  rw [h2, eV, eF, ep, map_nsmul, h1, nsmul_eq_mul, pow_one]
  congr 1
  rw [WittVector.frobenius_eq_map_frobenius]
  congr 2
  exact RingHom.ext fun r => frobRing_apply hp r

end GlobalTheory.Dieu.EtFromConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem addHom_eq_of_basis {R S M ι : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (ρ : R →+* S) (F₁ F₂ : M →+ S)
    (h₁ : ∀ (c : R) x, F₁ (c • x) = ρ c * F₁ x) (h₂ : ∀ (c : R) x, F₂ (c • x) = ρ c * F₂ x)
    (h : ∀ i, F₁ (b i) = F₂ (b i)) (x : M) : F₁ x = F₂ x := by
  have hx : x ∈ Submodule.span R (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
  | smul c y _ hy => rw [h₁, h₂, hy]

theorem wittMap_comp (p : ℕ) [Fact p.Prime] {k k' k'' : Type} [CommRing k] [CommRing k'] [CommRing k'']
    (σ : k →+* k') (τ : k' →+* k'') (x : WittVector p k) :
    WittVector.map (τ.comp σ) x = WittVector.map τ (WittVector.map σ x) := by
  ext n
  simp [WittVector.map_coeff]

end GlobalTheory.Dieu.EtFromConn

theorem GlobalTheory.Dieu.EtFromConn.isTr_comp : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' k'' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] (σ : k →+* k') (τ : k' →+* k'') (υ : k →+* k'') (G'' : PDivGroup p k'') (G' : PDivGroup p k') (G : PDivGroup p k) (h'' : G''.IsEt) (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G), (∀ n a, u.app n a = t.app n (s.app n a)) → ∀ (l : Mod B G h) (l' : Mod B G' h') (l'' : Mod B G'' h''), IsTr B σ h' h s l l' → IsTr B τ h'' h' t l' l'' → IsTr B υ h'' h u l l'' := by
  intro p _ B k k' k'' _ _ _ _ _ _ _ _ _ σ τ υ G'' G' G h'' h' h s t u hu l l' l'' hs ht
  have hυ : υ = τ.comp σ := by
    ext r
    have e := congrArg (Coalgebra.counit (R := k'')) (hu 0 (algebraMap k (G.A 0) r))
    rw [(u.app 0).counit_map, (t.app 0).counit_map, (s.app 0).counit_map,
      Bialgebra.counit_algebraMap] at e
    simpa using e
  subst hυ
  obtain rfl : u = t.comp s := SemiHom.ext_apply hu
  letI iσ : Algebra k k' := σ.toAlgebra
  letI iτ : Algebra k' k'' := τ.toAlgebra
  letI iυ : Algebra k k'' := (τ.comp σ).toAlgebra
  dsimp only [IsTr] at hs ht ⊢
  obtain ⟨hb, lb, hlb, hl'⟩ := hs
  obtain ⟨hb', lb', hlb', hl''⟩ := ht
  have hD := dual_conn h
  have hbu : (G.dual.baseChange k'').IsConn := (baseChange_isConn_isEt p k k'' G.dual).1 hD
  haveI := B.free G.dual hD
  haveI := B.finite G.dual hD
  let b := Module.Free.chooseBasis (WittVector p k) (B.M G.dual hD)
  obtain ⟨bu, hbu_eq⟩ := _root_.GlobalTheory.Dieu.Base.smap_toBase_basis p _ B k k'' G.dual hD hbu _ b
  obtain ⟨bk, hbk_eq⟩ := _root_.GlobalTheory.Dieu.Base.smap_toBase_basis p _ B k k' G.dual hD hb _ b
  let lbu : Module.Dual (WittVector p k'') (B.M (G.dual.baseChange k'') hbu) :=
    bu.constr (WittVector p k'') fun i => WittVector.map (τ.comp σ) (l (b i))
  have hlbu : ∀ x, lbu (B.smap hbu hD (G.dual.toBase k'') x) = WittVector.map (τ.comp σ) (l x) := by
    intro x
    refine addHom_eq_of_basis b (WittVector.map (τ.comp σ))
      ((lbu : _ →+ WittVector p k'').comp (B.smap hbu hD (G.dual.toBase k'')))
      ((WittVector.map (τ.comp σ)).toAddMonoidHom.comp (l : _ →+ WittVector p k)) ?_ ?_ ?_ x
    · intro c x
      show lbu (B.smap hbu hD (G.dual.toBase k'') (c • x)) = _ * lbu (B.smap hbu hD (G.dual.toBase k'') x)
      rw [B.smap_smul, LinearMap.map_smul, smul_eq_mul]
      rfl
    · intro c x
      simp [map_smul, smul_eq_mul, map_mul]
    · intro i
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe]
      rw [← hbu_eq, Module.Basis.constr_basis]
  refine ⟨hbu, lbu, hlbu, fun y => ?_⟩

  let β : G'.baseChange k'' ⟶ G.baseChange k'' :=
    SemiHom.lift (((G'.toBase k'').comp s : SemiHom ((algebraMap k' k'').comp σ) _ G) :
      SemiHom (algebraMap k k'') _ G)
  have hβ : ∀ n (b : G.A n), β.app n ((G.toBase k'').app n b) = (G'.toBase k'').app n (s.app n b) := by
    intro n b
    rw [toBase_app, SemiHom.lift_app, one_smul]
    rfl
  have hlift : (t.comp s).lift = t.lift ≫ β := baseChange_hom_ext fun n a => by
    rw [SemiHom.lift_app, one_smul, comp_app, BialgHom.comp_apply, ← toBase_app, hβ, toBase_app,
      SemiHom.lift_app, one_smul]
    rfl
  let φs := (PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift
  let φt := (PerfdLat.dualBaseChange k'' G').inv ≫ dualHom G'' (G'.baseChange k'') t.lift
  let ψ : G.dual.baseChange k'' ⟶ G'.dual.baseChange k'' :=
    (PerfdLat.dualBaseChange k'' G).inv ≫ dualHom _ _ β ≫ (PerfdLat.dualBaseChange k'' G').hom
  have hψ : (PerfdLat.dualBaseChange k'' G).inv ≫ dualHom G'' (G.baseChange k'') (t.comp s).lift =
      ψ ≫ φt := by
    simp only [hlift, dualHom_comp, ψ, φt, Category.assoc, Iso.hom_inv_id_assoc]
  let ρ : SemiHom τ (G.dual.baseChange k'') (G.dual.baseChange k') :=
    (G.dual.toBase k'').liftOver τ (fun _ => rfl)
  have hρ : ∀ n (χ : G.dual.A n), ρ.app n ((G.dual.toBase k').app n χ) = (G.dual.toBase k'').app n χ := by
    intro n χ
    rw [toBase_app, SemiHom.liftOver_app, map_one, one_smul]
  have hinv : ∀ {O' : Type} [Field O'] [Algebra k O'] (n : ℕ) (Z : (G.baseChange O').dual.A n),
      (PerfdLat.dualBaseChange O' G).hom.app n ((PerfdLat.dualBaseChange O' G).inv.app n Z) = Z :=
    fun {O'} _ _ n Z => DFunLike.congr_fun (congrArg (fun f => Hom.app f n) (PerfdLat.dualBaseChange O' G).hom_inv_id) Z
  have hinj : ∀ n, Function.Injective ((PerfdLat.dualBaseChange k'' G).hom.app n) := fun n x y hxy => by
    have e : ∀ x, (PerfdLat.dualBaseChange k'' G).inv.app n ((PerfdLat.dualBaseChange k'' G).hom.app n x) = x :=
      fun x => DFunLike.congr_fun (congrArg (fun f => Hom.app f n) (PerfdLat.dualBaseChange k'' G).inv_hom_id) x
    rw [← e x, ← e y, hxy]
  have hE : ∀ n (y : (G.dual.baseChange k').A n) (b : G.A n),
      ((PerfdLat.dualBaseChange k'' G).hom.app n (ρ.app n y)).ofConv ((G.toBase k'').app n b) =
        τ (((PerfdLat.dualBaseChange k' G).hom.app n y).ofConv ((G.toBase k').app n b)) := by
    intro n y b
    induction y using baseChange_induction k' (G := G.dual) n with
    | h0 => simp
    | h1 r χ =>
      rw [(ρ.app n).smul_map, map_smul, WithConv.ofConv_smul, LinearMap.smul_apply, map_smul, WithConv.ofConv_smul,
        LinearMap.smul_apply, hρ, dualBaseChange_toBase, dualBaseChange_toBase, smul_eq_mul, smul_eq_mul,
        map_mul]
      rfl
    | h2 z w hz hw =>
      rw [map_add (f := _), map_add (f := _), WithConv.ofConv_add, LinearMap.add_apply, map_add (f := _), WithConv.ofConv_add, LinearMap.add_apply,
        map_add, hz, hw]
  have hC : ∀ n a, ψ.app n ((G'.dual.toBase k'').app n a) = ρ.app n (φs.app n a) := by
    intro n a
    apply hinj n
    apply WithConv.ofConv_injective
    refine LinearMap.ext fun x => ?_
    induction x using baseChange_induction k'' (G := G) n with
    | h0 => simp
    | h1 r b =>
      rw [map_smul, map_smul, hE]
      congr 1
      change ((PerfdLat.dualBaseChange k'' G).hom.app n ((PerfdLat.dualBaseChange k'' G).inv.app n
        (CartierDual.map (β.app n) ((PerfdLat.dualBaseChange k'' G').hom.app n ((G'.dual.toBase k'').app n a))))).ofConv
          ((G.toBase k'').app n b) = τ (((PerfdLat.dualBaseChange k' G).hom.app n ((PerfdLat.dualBaseChange k' G).inv.app n
            (CartierDual.map (s.lift.app n) a))).ofConv ((G.toBase k').app n b))
      rw [hinv, hinv, CartierDual.map_apply, CartierDual.map_apply, hβ, dualBaseChange_toBase, toBase_app,
        SemiHom.lift_app, one_smul]
      rfl
    | h2 z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw]
  have hD' : ∀ v, lbu (B.smap hbu hb ρ v) = WittVector.map τ (lb v) := by
    intro v
    refine addHom_eq_of_basis bk (WittVector.map τ) ((lbu : _ →+ WittVector p k'').comp (B.smap hbu hb ρ))
      ((WittVector.map τ).toAddMonoidHom.comp (lb : _ →+ WittVector p k')) ?_ ?_ ?_ v
    · intro c x
      show lbu (B.smap hbu hb ρ (c • x)) = _ * lbu (B.smap hbu hb ρ x)
      rw [B.smap_smul, LinearMap.map_smul, smul_eq_mul]
    · intro c x
      simp [map_smul, smul_eq_mul, map_mul]
    · intro i
      show lbu (B.smap hbu hb ρ (bk i)) = WittVector.map τ (lb (bk i))
      rw [hbk_eq, hlb, ← B.smap_comp hbu hb hD (G.dual.toBase k') ρ (G.dual.toBase k'')
        (fun n a => (hρ n a).symm), hlbu, wittMap_comp]
  have hA : ∀ z, lb' z = lbu (B.map hbu hb' ψ z) := by
    haveI := B.free G'.dual (dual_conn h')
    haveI := B.finite G'.dual (dual_conn h')
    let b' := Module.Free.chooseBasis (WittVector p k') (B.M G'.dual (dual_conn h'))
    obtain ⟨b'', hb''⟩ := _root_.GlobalTheory.Dieu.Base.smap_toBase_basis p _ B k' k'' G'.dual (dual_conn h') hb' _ b'
    have key := b''.ext (f₁ := lb') (f₂ := lbu.comp (B.map hbu hb' ψ)) fun i => by
      rw [hb'', hlb', hl', LinearMap.comp_apply]
      change _ = lbu (B.smap hbu hb' (SemiHom.ofHom ψ)
        (B.smap hb' (dual_conn h') (G'.dual.toBase k'') (b' i)))
      rw [← B.smap_comp hbu hb' (dual_conn h') (G'.dual.toBase k'') (SemiHom.ofHom ψ)
        (ρ.comp (SemiHom.ofHom φs)) (fun n a => (hC n a).symm),
        B.smap_comp hbu hb (dual_conn h') (SemiHom.ofHom φs) ρ (ρ.comp (SemiHom.ofHom φs)) (fun _ _ => rfl),
        hD']
      rfl
    exact fun z => LinearMap.congr_fun key z
  rw [hl'', hA, hψ]
  exact congrArg lbu (B.smap_comp hbu hb' (dual_conn h'') (SemiHom.ofHom φt) (SemiHom.ofHom ψ)
    (SemiHom.ofHom (ψ ≫ φt)) (fun _ _ => rfl) y).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeEqRigidifiedExtensionPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem rigToLie_toBase_rig {p : ℕ} [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [Field k']
    [CharP k' p] [Algebra k k'] (G : PDivGroup p k) (r : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (w : G.dual.omega) :
    (G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig r)
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom ((G.dual.toBase k').omega w)) =
      algebraMap k k' (G.rigToLie (p_eq_zero p k) r w) := by
  set_option backward.isDefEq.respectTransparency false in
   change (G.baseChange k').primLie ((G.baseChange k').extChar (p_eq_zero p k')
    ((G.baseChange k').rigToExt ((G.toBase k').rig r))) _ =
    algebraMap k k' (G.primLie (G.extChar (p_eq_zero p k) (G.rigToExt r)) w)
  set_option backward.isDefEq.respectTransparency false in
   rw [SemiHom.rigToExt_rig, SemiHom.extChar_vecExt _ (p_eq_zero p k)]
  exact primLie_toBase G _ w

theorem linearMap_eq_of_liftSemi_surjective {R R' M N : Type} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N]
    (f : M →ₛₗ[algebraMap R R'] N) (hf : Function.Surjective (liftSemi f)) (F₁ F₂ : N →ₗ[R'] R')
    (h : ∀ m, F₁ (f m) = F₂ (f m)) : F₁ = F₂ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨t, rfl⟩ := hf v
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r m => rw [liftSemi_tmul, map_smul, map_smul, h]

set_option maxHeartbeats 2000000 in
theorem red_of_isTr (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type)
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k) (h' : G'.IsEt) (h : G.IsEt)
    (s : SemiHom σ G' G) (l : Mod B G h) (l' : Mod B G' h') (hT : IsTr B σ h' h s l l') :
    red B G' h' l' = s.rig (red B G h l) := by
  letI : Algebra k k' := σ.toAlgebra
  obtain ⟨hb, lb, h1, h2⟩ := hT
  haveI := B.free _ hb
  haveI := B.finite _ hb
  obtain ⟨r', hr', -, -⟩ := wittDual_reduction p k' _ _ (B.red _ hb) (B.red_surjective _ hb)
    (B.red_eq_zero _ hb)
  have hψ : ∀ m, r' lb (B.red _ hb m) = WittVector.constantCoeff (lb m) := hr' lb
  have key1 : ∀ w : G.dual.omega,
      r' lb ((G.dual.baseChange k').rigOfOmega ((G.dual.toBase k').omega w)) =
        σ (G.rigToLie (p_eq_zero p k) (red B G h l) w) := by
    intro w
    obtain ⟨x, hx⟩ := B.red_surjective _ (dual_conn h) (G.dual.rigOfOmega w)
    have e1 : (G.dual.baseChange k').rigOfOmega ((G.dual.toBase k').omega w) =
        B.red _ hb (B.smap hb (dual_conn h) (G.dual.toBase k') x) := by
      rw [B.red_smap, hx, SemiHom.rig_rigOfOmega]
    have e2 : G.rigToLie (p_eq_zero p k) (red B G h l) w = WittVector.constantCoeff (l x) := by
      rw [rigToLie_red, LinearMap.dualMap_apply, ← hx]
      exact (redDual_spec B G h).1 l x
    have e3 : WittVector.constantCoeff (WittVector.map σ (l x)) = σ (WittVector.constantCoeff (l x)) := by
      simp [WittVector.constantCoeff_apply, WittVector.map_coeff]
    exact (congrArg (r' lb) e1).trans ((hψ _).trans ((congrArg _ (h1 x)).trans (e3.trans (congrArg σ e2.symm))))
  have key2 : ((G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig (red B G h l))).comp
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom) =
      (r' lb).comp (G.dual.baseChange k').rigOfOmega :=
    linearMap_eq_of_liftSemi_surjective (G.dual.toBase k').omega
      (T.omega_baseChange_bijective_of_p_eq_zero G.dual k' (p_eq_zero p k)).2 _ _ fun w => by
        set_option backward.isDefEq.respectTransparency false in
          simp only [LinearMap.comp_apply]
          rw [rigToLie_toBase_rig]
          exact (key1 w).symm
  have hinj := (PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k'
    (p_eq_zero p k') G' h').1.1
  apply hinj
  rw [rigToLie_red]
  refine LinearMap.ext fun w' => ?_
  rw [LinearMap.dualMap_apply]
  obtain ⟨x', hx'⟩ := B.red_surjective _ (dual_conn h') (G'.dual.rigOfOmega w')
  have hs : ∀ n a, s.app n a = (SemiHom.ofHom s.lift).app n ((G.toBase k').app n a) := fun n a => by
    rw [SemiHom.ofHom_app, toBase_app, SemiHom.lift_app, one_smul]
  have e4 : B.red _ hb (B.map hb (dual_conn h')
      ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) x') =
      (G.dual.baseChange k').rigOfOmega (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv
        (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w')) := by
    change B.red _ hb (B.smap hb (dual_conn h') (SemiHom.ofHom _) x') = _
    rw [B.red_smap, hx', SemiHom.rig_rigOfOmega, SemiHom.ofHom_omega, omegaMap_comp,
      LinearMap.comp_apply]
  have e5 : G'.rigToLie (p_eq_zero p k') (s.rig (red B G h l)) w' =
      (G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig (red B G h l))
        (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w') := by
    rw [← (G.toBase k').rig_rig (SemiHom.ofHom s.lift) s hs, SemiHom.ofHom_rig,
      rigToLie_rigExtMap, lieMap_apply]
  have e6 : ∀ v, omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv v) = v := fun v => by
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply]
  rw [← hx', (redDual_spec B G' h').1, h2, ← hψ, e4, e5]
  have e7 := LinearMap.congr_fun key2 (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv
    (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w'))
  simp only [LinearMap.comp_apply, e6] at e7
  exact e7.symm

end GlobalTheory.Dieu.EtFromConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeOfHomEqCompDualHom
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem isTr_ofHom : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H) (l : Mod B H hH), IsTr B (RingHom.id k) hG hH (SemiHom.ofHom f) l (l ∘ₗ B.map (dual_conn hH) (dual_conn hG) (dualHom G H f)) := by
  intro p _ B k _ _ _ G H hG hH f l
  unfold IsTr
  letI : Algebra k k := (RingHom.id k).toAlgebra
  have hd := dual_conn hH
  have hd' := dual_conn hG
  have hb : (H.dual.baseChange k).IsConn := (baseChange_isConn_isEt p k k H.dual).1 hd
  let φ : H.dual ⟶ H.dual.baseChange k := SemiHom.lift (SemiHom.ofHom (𝟙 H.dual))
  have hφ : ∀ x, B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd (H.dual.toBase k) x) = x := by
    intro x
    rw [← B.smap_comp hd hb hd (H.dual.toBase k) (SemiHom.ofHom φ) (SemiHom.ofHom (𝟙 _)), B.smap_id]
    intro n a
    exact ((SemiHom.lift_app _ n 1 a).trans (one_smul _ _)).symm
  refine ⟨hb, l ∘ₗ B.map hd hb φ, fun x => ?_, fun y => ?_⟩
  · change l (B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd (H.dual.toBase k) x)) = _
    rw [hφ, WittVector.map_id, RingHom.id_apply]
  · have hc : ∀ n a, (SemiHom.ofHom ((PerfdLat.dualBaseChange k H).inv ≫
        dualHom G (H.baseChange k) (SemiHom.ofHom f).lift)).app n a =
        (H.dual.toBase k).app n ((SemiHom.ofHom (dualHom G H f)).app n a) := by
      intro n a
      change (CartierDual.baseChange k k (H.A n)).symm (CartierDual.map ((SemiHom.ofHom f).lift.app n) a) = (1 : k) ⊗ₜ CartierDual.map (f.app n) a
      apply EquivLike.injective (CartierDual.baseChange k k (H.A n))
      rw [BialgEquiv.apply_symm_apply]
      refine WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun b m => ?_)
      simp
      rw [SemiHom.lift_app, SemiHom.ofHom_app, map_smul, smul_eq_mul, mul_comm]
    have key := B.smap_comp hb hd hd' (SemiHom.ofHom (dualHom G H f)) (H.dual.toBase k) _ hc y
    change l (B.map hd hd' (dualHom G H f) y) = l (B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd' _ y))
    rw [key, hφ]
    rfl

end GlobalTheory.Dieu.EtFromConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeSemilinearHomDualGroups
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory

theorem semiHom_dual_transpose : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (G' : PDivGroup p k') (hd : G.dual.IsConn) (hd' : G'.dual.IsConn) (hb : (G.dual.baseChange k').IsConn) (s : SemiHom (algebraMap k k') G' G) (l : Module.Dual (WittVector p k) (B.M G.dual hd)), ∃! l' : Module.Dual (WittVector p k') (B.M G'.dual hd'), ∃ lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb), (∀ x, lb (B.smap hb hd (G.dual.toBase k') x) = WittVector.map (algebraMap k k') (l x)) ∧ ∀ y, l' y = lb (B.map hb hd' ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) y) := by
  intro p _ B k k' _ _ _ _ _ _ _ G G' hd hd' hb s l
  haveI := B.free G.dual hd
  haveI := B.finite G.dual hd
  let b := Module.Free.chooseBasis (WittVector p k) (B.M G.dual hd)
  obtain ⟨b', hb'⟩ := _root_.GlobalTheory.Dieu.Base.smap_toBase_basis p (fun _ _ G => G.IsConn) B k k' G.dual hd hb _ b
  let lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb) :=
    b'.constr (WittVector p k') (fun i => WittVector.map (algebraMap k k') (l (b i)))
  have h1 : ∀ x, lb (B.smap hb hd (G.dual.toBase k') x) = WittVector.map (algebraMap k k') (l x) := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, B.smap_smul, map_smul, ← hb', lb, Module.Basis.constr_basis, smul_eq_mul, map_mul]
  refine ⟨lb ∘ₗ B.map hb hd' ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift),
    ⟨lb, h1, fun y => rfl⟩, fun l'' ⟨lb', h1', h2'⟩ => ?_⟩
  have hl : lb' = lb := b'.ext fun i => by
    simp only [lb, Module.Basis.constr_basis]
    rw [hb', h1']
  subst hl
  exact LinearMap.ext fun y => h2' y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicEndomorphismLattice
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_endomorphism_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  first | (exact @GlobalTheory.LKGeo.ModLim.exists_limit) | (exact GlobalTheory.LKGeo.ModLim.exists_limit) | (intros; apply GlobalTheory.LKGeo.ModLim.exists_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedPDivGroupChartOfIsConnStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connectedPDivGroupChart_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.IsConn → ∃ d, Nonempty (Chart G d) := by
  first | exact @GlobalTheory.Katz.exists_chart_of_isConn | exact GlobalTheory.Katz.exists_chart_of_isConn | (intros; apply GlobalTheory.Katz.exists_chart_of_isConn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientOfGaloisStableFiniteSubgroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ deg q = Nat.card G ∧ (ptMap q).ker = G ∧ ∀ (C : AbVar K) (f : A ⟶ C), G ≤ (ptMap f).ker → ∃ g : B ⟶ C, q ≫ g = f := by
  first | (exact @GlobalTheory.AV.AbVar.exists_quot_of_galois_stable) | (exact GlobalTheory.AV.AbVar.exists_quot_of_galois_stable) | (intros; apply GlobalTheory.AV.AbVar.exists_quot_of_galois_stable  <;> assumption)
end

