module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.EtaleCohomology.EtaleSheaves.Bundle0015
public import Development.EtaleCohomology.TateTwists.Bundle0012
public import Development.EtaleCohomology.EtaleSheaves.LeafSSCut

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRootLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafRootLocPf

def kpair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) : StandardEtalePair A where
  f := X ^ q - C u
  monic_f := monic_X_pow_sub_C _ (NeZero.ne q)
  g := X
  cond := ⟨C c * X, 0, q, by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    subst hk
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [show (C (((k + 1 : ℕ) : A)) * X ^ k) * (C c * X) = C (c * ((k + 1 : ℕ) : A)) * X ^ (k + 1) by
      rw [C_mul, pow_succ]; ring]
    rw [hc, C_1, one_mul]⟩

theorem kpair_root {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) :
    (kpair q c hc u).X ^ q = algebraMap A (kpair q c hc u).Ring u := by
  have h : aeval (kpair q c hc u).X (X ^ q - C u) = 0 := (kpair q c hc u).hasMap_X.1
  rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

theorem kpair_surj {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : Aˣ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (kpair q c hc (u : A)).Ring)) := by
  intro p
  let K := p.asIdeal.ResidueField
  let Ω := AlgebraicClosure K
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω u) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hu : IsUnit (algebraMap A Ω u) := u.isUnit.map _
  have hzu : IsUnit z := by
    rw [← hz] at hu; exact (isUnit_pow_iff (NeZero.ne q)).mp hu
  have hm : (kpair q c hc (u : A)).HasMap z := by
    refine ⟨?_, ?_⟩
    · simp [kpair, hz]
    · simpa [kpair] using hzu
  let ψ := (kpair q c hc (u : A)).lift z hm
  refine ⟨⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  ext1
  change Ideal.comap _ (RingHom.ker ψ.toRingHom) = p.asIdeal
  rw [RingHom.comap_ker, show ψ.toRingHom.comp (algebraMap A _) = algebraMap A Ω from ψ.comp_algebraMap]
  rw [IsScalarTower.algebraMap_eq A K Ω, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap K Ω).injective, ← RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

theorem loc_of_cover {U Y : Scheme.{0}} (π : Y ⟶ U) [Etale π] [Surjective π]
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : ∀ (V : Scheme.{0}) (h : V ⟶ Y), P V (h ≫ π)) : Loc U P := by
  let 𝒰 : U.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers PUnit.{1} (fun _ => Y) (fun _ => π)
      (fun x => ⟨PUnit.unit, π.surjective x⟩) inferInstance
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩
  intro V g hg
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact hP V h

theorem LeafRootLoc_of : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc := by
  intro q _ U hq u
  obtain ⟨c, hc⟩ := hq.exists_left_inv
  let P := kpair q c hc (u : Γ(U, ⊤))
  let B : CommRingCat.{0} := CommRingCat.of P.Ring
  let φ : Γ(U, ⊤) ⟶ B := CommRingCat.ofHom (algebraMap _ P.Ring)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨kpair_surj q c hc u⟩
  refine loc_of_cover (pullback.fst U.toSpecΓ (Spec.map φ)) _ fun V h => ?_
  have hX : IsUnit P.X := (isUnit_pow_iff (NeZero.ne q)).mp (by rw [kpair_root]; exact u.isUnit.map _)
  have e : (h ≫ pullback.snd _ _) ≫ Spec.map φ = (h ≫ pullback.fst _ _) ≫ U.toSpecΓ := by
    simp [pullback.condition]
  have hcomp : φ ≫ (Scheme.ΓSpecIso B).inv ≫ (h ≫ pullback.snd _ _).appTop = (h ≫ pullback.fst _ _).appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop, e,
      Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨Units.map ((h ≫ pullback.snd _ _).appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom).toMonoidHom hX.unit, ?_⟩
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  rw [← map_pow, kpair_root]
  exact congrArg (fun f => f.hom (u : Γ(U, ⊤))) hcomp

end LateralTheory.E.LeafRootLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSelPicPf
section
noncomputable section
open nonZeroDivisors IsDedekindDomain

namespace LateralTheory.E.LeafSelPicPf
open LateralTheory.E.LeafPicCut

lemma units_torsionFree {B : Type} [CommRing B] [IsDedekindDomain B] {q : ℕ} (hq : q ≠ 0)
    (x : (FractionalIdeal B⁰ (FractionRing B))ˣ) (h : x ^ q = 1) : x = 1 := by
  have hx0 : (x : FractionalIdeal B⁰ (FractionRing B)) ≠ 0 := x.ne_zero
  have hc : ∀ v : HeightOneSpectrum B,
      FractionalIdeal.count (FractionRing B) v (x : FractionalIdeal B⁰ (FractionRing B)) = 0 := by
    intro v
    have h1 := FractionalIdeal.count_pow (FractionRing B) v q (x : FractionalIdeal B⁰ (FractionRing B))
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one, FractionalIdeal.count_one] at h1
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    exact (mul_eq_zero.mp h1.symm).resolve_left hq'
  ext1
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (FractionRing B) hx0]
  simp [hc]

lemma exists_rep {B : Type} [CommRing B] [IsDedekindDomain B] (q : ℕ) (c : ClassGroup B) (hc : c ^ q = 1) :
    ∃ (I : (FractionalIdeal B⁰ (FractionRing B))ˣ) (f : (FractionRing B)ˣ),
      ClassGroup.mk (FractionRing B) I = c ∧ toPrincipalIdeal B (FractionRing B) f = I ^ q := by
  revert hc
  refine ClassGroup.induction (R := B) (FractionRing B) (fun I hc => ?_) c
  · refine ⟨I, ?_⟩
    have h1 : ClassGroup.mk (FractionRing B) (I ^ q) = ClassGroup.mk (FractionRing B) 1 := by
      rw [map_pow, hc, map_one]
    obtain ⟨x, hx⟩ := ClassGroup.mk_eq_mk.mp h1
    refine ⟨x⁻¹, rfl, ?_⟩
    rw [map_inv, inv_eq_iff_mul_eq_one, mul_comm, hx]

theorem LeafSelPic_of : LeafSelPic := by
  intro B _ _ q _ hfin
  classical
  have hex := fun c : {c : ClassGroup B // c ^ q = 1} => exists_rep q c.1 c.2
  choose I f hI hf using hex
  have hsel : ∀ c, f c ∈ sel B q := fun c => by
    simp only [sel, Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨I c, by rw [hf c]; rfl⟩
  let φ : {c : ClassGroup B // c ^ q = 1} → selQ B q := fun c => QuotientGroup.mk ⟨f c, hsel c⟩
  refine Finite.of_injective φ ?_
  intro c d hcd
  have h1 := QuotientGroup.eq.mp hcd
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hu
  have hx : ((I c)⁻¹ * I d * (toPrincipalIdeal B (FractionRing B) u)⁻¹) ^ q = 1 := by
    rw [mul_pow, mul_pow, inv_pow, inv_pow, ← map_pow, hu, ← hf c, ← hf d, map_mul, map_inv]
    group
  have h2 := units_torsionFree (NeZero.ne q) _ hx
  apply Subtype.ext
  rw [← hI c, ← hI d]
  refine ClassGroup.mk_eq_mk.mpr ⟨u, ?_⟩
  rw [mul_inv_eq_one, inv_mul_eq_iff_eq_mul] at h2
  exact h2.symm

end LateralTheory.E.LeafSelPicPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensFactorPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.E.LeafTensFactorPf

theorem lift_lof {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    τ.lift U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)
      ⟨(s, t), hw⟩ (a ⊗ₜ b)) = τ.mul U s t w hw a b := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]

theorem uniq_mul {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) {M : Shv R}
    (ψ ψ' : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec M U)
    (hψ : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ U y) = ψ V (Sec.res g y))
    (hψ' : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ' U y) = ψ' V (Sec.res g y))
    (h : ∀ U s t (hw : s + t = w) a b, ψ U (τ.mul U s t w hw a b) = ψ' U (τ.mul U s t w hw a b))
    (U : Scheme.{0}) (y : Sec (T.X w) U) : ψ U y = ψ' U y := by
  have hl : ∀ V (x : Tens I J V w), ψ V (τ.lift V w x) = ψ' V (τ.lift V w x) := by
    intro V x
    classical
    induction x using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _)]; rw [ha, hb]
    | of p z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _)]; rw [ha, hb]
      | tmul a c =>
        obtain ⟨⟨s, t⟩, hw⟩ := p
        rw [lift_lof]
        exact h V s t hw a c
  apply LateralTheory.EtaleFoundations.TensFam.sep M
  obtain ⟨S, hS, h1⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := h1 V g hg
  rw [hψ, hψ', ← hx, hl]

theorem secMap_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map f y) = Sec.map f (Sec.res g y) := by
  have := f.hom.naturality g.op
  exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) y) this).symm

theorem addHom_usmul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (n : ℤˣ) (x : A) :
    φ (n • x) = n • φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

end LateralTheory.E.LeafTensFactorPf

namespace LateralTheory.E.LeafTensFactorPf

theorem phi_exists {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ) :
    ∃ φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧
      ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b := by
  obtain ⟨φ, h1, h2⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing R R τ hτ w (K.X w)
    (fun U => (ν.lift U w).toAddMonoidHom) (fun V U g x => LateralTheory.EtaleFoundations.TensFam.lift_res ν g w x)
  refine ⟨φ, h1, fun U s t hw a b => ?_⟩
  have := h2 U (DirectSum.of _ ⟨(s, t), hw⟩ (a ⊗ₜ b))
  rw [lift_lof] at this
  rw [this]
  exact lift_lof ν U s t w hw a b

theorem phi_smul {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ)
    (φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (h2 : ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b)
    (U : Scheme.{0}) (r : ULift.{1} R) (y : Sec (T.X w) U) : φ U (r • y) = r • φ U y := by
  refine uniq_mul τ hτ w (fun U => (φ U).comp (DistribSMul.toAddMonoidHom _ r))
    (fun U => (DistribSMul.toAddMonoidHom _ r).comp (φ U)) ?_ ?_ ?_ U y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [h1]; congr 1; exact map_smul _ r y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← h1]; exact map_smul _ r _
  · intro U s t hw a b
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← LinearMap.map_smul₂, h2, h2, LinearMap.map_smul₂]

def toHom {R : Type} [CommRing R] {F G : Shv R} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (hsm : ∀ U (r : ULift.{1} R) y, φ U (r • y) = r • φ U y) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom { toFun := φ (unop U), map_add' := map_add _, map_smul' := hsm (unop U) }
      naturality := fun U V g => by
        ext y
        exact (hnat _ _ g.unop y).symm }

theorem sheafHom_ext {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = Sec.map g y) : f = g := by
  apply Sheaf.hom_ext
  ext U y
  exact h (unop U) y

theorem factor {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) :
    ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u := by
  choose φ h1 h2 using fun w => phi_exists τ hτ ν w
  have hsm : ∀ w U (r : ULift.{1} R) y, φ w U (r • y) = r • φ w U y :=
    fun w => phi_smul τ hτ ν w (φ w) (h1 w) (h2 w)
  refine ⟨{ f := fun w => toHom (φ w) (h1 w) (hsm w), comm' := ?_ }, ?_⟩
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    apply sheafHom_ext
    intro U y
    show Sec.map (K.d i (i + 1)) (φ i U y) = φ (i + 1) U (Sec.map (T.d i (i + 1)) y)
    refine uniq_mul τ hτ i (M := K.X (i + 1))
      (fun U => ((K.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom.comp (φ i U))
      (fun U => (φ (i + 1) U).comp ((T.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom) ?_ ?_ ?_ U y
    · intro V U g y
      show Sec.res g (Sec.map (K.d i (i + 1)) (φ i U y)) = Sec.map (K.d i (i + 1)) (φ i V (Sec.res g y))
      rw [secMap_nat, h1]
    · intro V U g y
      show Sec.res g (φ (i + 1) U (Sec.map (T.d i (i + 1)) y)) = φ (i + 1) V (Sec.map (T.d i (i + 1)) (Sec.res g y))
      rw [h1, secMap_nat]
    · intro U s t hw a b
      show Sec.map (K.d i (i + 1)) (φ i U (τ.mul U s t i hw a b)) = φ (i + 1) U (Sec.map (T.d i (i + 1)) (τ.mul U s t i hw a b))
      rw [h2, ν.leibniz, τ.leibniz, map_add (f := _), addHom_usmul, h2, h2]
  · intro U s t w hw a b
    rw [LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f, LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f]
    exact h2 w U s t hw a b

end LateralTheory.E.LeafTensFactorPf

theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := by
  intro R _ I J T K τ hτ ν
  exact LateralTheory.E.LeafTensFactorPf.factor τ hτ ν
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTermsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafTermsPf

variable {R : Type} [CommRing R]

theorem HKpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem HKpull_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem finite_of_retract {K L : Cx R} (s : K ⟶ L) (t : L ⟶ K) (h : s ≫ t = 𝟙 K) (F : Shv R) (n : ℤ)
    (hL : Finite (HK R L F n)) : Finite (HK R K F n) :=
  Finite.of_surjective (HK.pull R s F n) (fun x =>
    ⟨HK.pull R t F n x, by rw [← HKpull_comp, h, HKpull_id]⟩)

theorem finite_of_iso {A B : Shv R} (e : A ≅ B) (F : Shv R) (n : ℤ)
    (hB : Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj B) F n)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj A) F n) :=
  finite_of_retract _ _ (((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).mapIso e).hom_inv_id) F n hB

theorem d_const_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat
    (i := 1) (j := 0) (i' := -1) (j' := 0) rfl rfl
  change (((chainsN R).obj (disc.obj P)).extend ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [h]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    simp [chainsN, Fin.sum_univ_two, SimplicialObject.δ, disc]
    all_goals first
      | (erw [neg_one_smul, one_smul, add_neg_cancel])
      | (simp only [one_smul, neg_smul]; exact add_neg_cancel _)
      | abel
    all_goals rfl
  rw [this]; simp

def proj0 (P : PSh) : (chains R).obj (disc.obj P) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (((chains R).obj (disc.obj P)).X 0) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi => by
    have : i = -1 := by simp at hi; omega
    subst this; rw [d_const_zero]; simp)

theorem etale_chain_complex_degree_zero_incl_proj_eq_id (P : PSh) : LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (disc.obj P)) ≫ proj0 P = 𝟙 _ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [LateralTheory.E.LeafSSCut.incl0, proj0]

theorem finite_single_of_H (Z : Scheme.{0}) (F : Shv R) (m : ℤ) (h : Finite (H R (sch.obj Z) F m)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj (yoneda.obj Z))) F m) :=
  finite_of_iso (chainsXIso R (disc.obj (yoneda.obj Z)) 0).symm F m
    (finite_of_retract _ _ (etale_chain_complex_degree_zero_incl_proj_eq_id (R := R) (yoneda.obj Z)) F m h)

section Geo
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

abbrev W (n : ℕ) : Scheme.{0} := widePullback X (fun _ : Fin n => Y) (fun _ => f)

def toPb (n : ℕ) : W f (n + 1) ⟶ pullback (WidePullback.base (fun _ : Fin n => f)) f :=
  pullback.lift (WidePullback.lift (WidePullback.base _) (fun j => WidePullback.π _ j.succ) (by simp))
    (WidePullback.π _ 0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

def ofPb (n : ℕ) : pullback (WidePullback.base (fun _ : Fin n => f)) f ⟶ W f (n + 1) :=
  WidePullback.lift (pullback.snd _ _ ≫ f)
    (Fin.cases (pullback.snd _ _) (fun j => pullback.fst _ _ ≫ WidePullback.π _ j))
    (by intro j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [pullback.condition, WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

theorem toPb_ofPb (n : ℕ) : toPb f n ≫ ofPb f n = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    simp only [Category.assoc, Category.id_comp]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_zero]; rw [toPb, pullback.lift_snd]
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_succ]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π]
  · simp only [Category.assoc, Category.id_comp]
    rw [ofPb, WidePullback.lift_base, toPb, pullback.lift_snd_assoc, WidePullback.π_arrow]

theorem ofPb_toPb (n : ℕ) : ofPb f n ≫ toPb f n = 𝟙 _ := by
  apply pullback.hom_ext
  · apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π, ofPb, WidePullback.lift_π]
      simp only [Fin.cases_succ]
    · simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base, ofPb, WidePullback.lift_base, pullback.condition]
  · simp only [Category.assoc, Category.id_comp]
    rw [toPb, pullback.lift_snd, ofPb, WidePullback.lift_π]
    simp only [Fin.cases_zero]

theorem base_zero_iso : IsIso (WidePullback.base (fun _ : Fin 0 => f)) :=
  ⟨⟨WidePullback.lift (𝟙 X) (fun j => j.elim0) (fun j => j.elim0), by
    refine ⟨WidePullback.hom_ext _ _ _ (fun j => j.elim0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]), by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]⟩⟩⟩

theorem base_proper [IsProper f] : ∀ n : ℕ, IsProper (WidePullback.base (fun _ : Fin n => f))
  | 0 => by
    have := base_zero_iso f
    first | infer_instance | exact MorphismProperty.of_isIso (P := @IsProper) _
  | n + 1 => by
    have := base_proper n
    have hi : IsIso (toPb f n) := ⟨⟨ofPb f n, toPb_ofPb f n, ofPb_toPb f n⟩⟩
    have : WidePullback.base (fun _ : Fin (n + 1) => f) = toPb f n ≫ pullback.fst _ _ ≫ WidePullback.base _ := by
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base]
    rw [this]
    infer_instance

def eIso (n : ℕ) : yoneda.obj (W f n) ≅ widePullback (yoneda.obj X) (fun _ : Fin n => yoneda.obj Y) (fun _ => yoneda.map f) :=
  preservesLimitIso yoneda _ ≪≫ HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

end Geo

theorem LeafTerms_of : LateralTheory.E.LeafSSCut.LeafTerms := by
  intro _ R _ F Y X f _ r m hZ
  refine finite_of_iso ((chainsXIso R (cech f) r) ≪≫ (free R).mapIso (eIso f (r + 1)).symm) F m ?_
  exact finite_single_of_H _ F m (hZ _ _ (base_proper f (r + 1)))

end LateralTheory.E.LeafTermsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwResHtpyPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwResHtpyPf

theorem res_isKInj (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem htpy_of_qiso {C : Type*} [Category C] [Abelian C] {K L I : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] [I.IsKInjective] (u u' : L ⟶ I) (h : f ≫ u = f ≫ u') :
    Nonempty (Homotopy u u') := by
  have hY := IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hY
  have hf : (HomotopyCategory.subcategoryAcyclic C).trW
      ((HomotopyCategory.quotient C _).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    assumption
  have hb := (hY _ hf).1
  have : (HomotopyCategory.quotient C _).map u = (HomotopyCategory.quotient C _).map u' := by
    apply hb
    simp only [← Functor.map_comp, h]
  exact ⟨HomotopyCategory.homotopyOfEq _ _ this⟩

theorem sh_ext {R : Type} [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {X : Shv R}
    (φ ψ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj P ⟶ X)
    (h : toSheafify Scheme.etaleTopology.{0} P ≫ φ.hom = toSheafify Scheme.etaleTopology.{0} P ≫ ψ.hom) : φ = ψ := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv P X).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

theorem tw_hom_ext (q : ℕ) (i : ℤ) {X : Shv (ZMod q)} (φ ψ : tw q i ⟶ X)
    (h : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) : φ = ψ := by
  apply sh_ext
  ext U : 2
  apply ModuleCat.hom_ext
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
  exact h U.unop ζ

end LateralTheory.E.LeafTwResHtpyPf

open LateralTheory.E.LeafTwResHtpyPf in
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := by
  intro q _ k T e hT u u' hu
  obtain ⟨_, ε, hε, he⟩ := hT
  have := res_isKInj (ZMod q) (tw q k)
  refine htpy_of_qiso ε u u' ?_
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have key : sglι (tw q k) ≫ ε.f 0 ≫ u.f 0 = sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0 := by
    apply tw_hom_ext
    intro U ζ
    have := hu U ζ
    rw [← he U ζ] at this
    exact this
  have h1 : ε.f 0 ≫ u.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  have h2 : ε.f 0 ≫ u'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  exact h1.trans ((congrArg _ key).trans h2.symm)
end
end

