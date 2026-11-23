module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNnrealValuationOfAddValuation
section
namespace GlobalTheory

open scoped NNReal

noncomputable def expNegTop : WithTop ℚ → ℝ≥0
  | ⊤ => 0
  | (q : ℚ) => ⟨Real.exp (-(q : ℝ)), (Real.exp_pos _).le⟩

@[simp] theorem expNegTop_top : expNegTop ⊤ = 0 := rfl

theorem expNegTop_coe (q : ℚ) : ((expNegTop (q : WithTop ℚ) : ℝ≥0) : ℝ) = Real.exp (-(q : ℝ)) := rfl

theorem expNegTop_zero : expNegTop 0 = 1 := by
  apply NNReal.coe_injective
  have h := expNegTop_coe 0
  simpa using h

theorem expNegTop_add (a b : WithTop ℚ) : expNegTop (a + b) = expNegTop a * expNegTop b := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      apply NNReal.coe_injective
      rw [← WithTop.coe_add, NNReal.coe_mul, expNegTop_coe, expNegTop_coe, expNegTop_coe,
        ← Real.exp_add]
      push_cast
      ring_nf

theorem expNegTop_le_iff (a b : WithTop ℚ) : expNegTop a ≤ expNegTop b ↔ b ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top =>
      rw [← NNReal.coe_le_coe, expNegTop_coe]
      simp only [expNegTop_top, NNReal.coe_zero, top_le_iff, WithTop.coe_ne_top, iff_false, not_le]
      exact Real.exp_pos _
    | coe b =>
      rw [← NNReal.coe_le_coe, expNegTop_coe, expNegTop_coe, Real.exp_le_exp, neg_le_neg_iff,
        Rat.cast_le, WithTop.coe_le_coe]

noncomputable def expNegValuation {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    Valuation F ℝ≥0 where
  toFun x := expNegTop (v x)
  map_zero' := by simp
  map_one' := by simp [expNegTop_zero]
  map_mul' x y := by rw [v.map_mul, expNegTop_add]
  map_add_le_max' x y := by
    rcases min_le_iff.mp (v.map_add x y) with h | h
    · exact le_max_of_le_left ((expNegTop_le_iff _ _).mpr h)
    · exact le_max_of_le_right ((expNegTop_le_iff _ _).mpr h)

theorem expNegValuation_apply {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x = expNegTop (v x) := rfl

theorem expNegValuation_le_one_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x ≤ 1 ↔ 0 ≤ v x := by
  rw [expNegValuation_apply, ← expNegTop_zero, expNegTop_le_iff]

theorem exists_nnreal_valuation_of_addValuation :
    ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)), ∃ v' : Valuation F NNReal,
      (∀ x y, v' x ≤ v' y ↔ v y ≤ v x) ∧ v'.Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  intro F _ v
  refine ⟨expNegValuation v, fun x y => expNegTop_le_iff _ _, ?_, ?_, ?_⟩
  · exact Subtype.val_injective
  · intro x
    exact (expNegValuation_le_one_iff v _).mpr x.2
  · intro r hr
    exact ⟨⟨r, (expNegValuation_le_one_iff v r).mp hr⟩, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeTateImage

open GlobalTheory.TangentPow GlobalTheory.GmPoints

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}

noncomputable def bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    specO O (DualNumber R) ⟶ G :=
  ptMap (dualBC (Algebra.ofId O R)) ≫ x.1

theorem fst_bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    ptMap (TrivSqZeroExt.fstHom O R R) ≫ bc R x = 1 := by
  have h : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (dualBC (Algebra.ofId O R)) =
      ptMap (Algebra.ofId O R) ≫ ptMap (TrivSqZeroExt.fstHom O O O) := by
    rw [ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 1
    refine AlgHom.ext fun y => ?_
    simp [dualBC, TrivSqZeroExt.lift_def, TrivSqZeroExt.algebraMap_eq_inl']
  rw [bc, ← Category.assoc, h, Category.assoc, x.2]
  exact comp_one _

theorem dualBC_fst {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (y : DualNumber R) : (dualBC φ y).fst = φ y.fst := by
  simp [dualBC, TrivSqZeroExt.lift_def]

theorem dualBC_snd {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (y : DualNumber R) : (dualBC φ y).snd = φ y.snd := by
  simp [dualBC, TrivSqZeroExt.lift_def]

theorem ptMap_bc {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (x : LieG G) : ptMap (dualBC φ) ≫ bc R x = bc R' x := by
  rw [bc, bc, ← Category.assoc, ptMap_comp_ptMap]
  congr 2
  refine AlgHom.ext fun y => ?_
  ext
  · simp only [AlgHom.comp_apply, dualBC_fst, Algebra.ofId_apply, AlgHom.commutes]
  · simp only [AlgHom.comp_apply, dualBC_snd, Algebra.ofId_apply, AlgHom.commutes]

theorem existsUnique_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : ∃! w : specO O (DualNumber R) ⟶ torsion G (p ^ n),
      w ≫ torsion.ι G (p ^ n) = bc R x :=
  (pow_eq_scale_and_existsUnique_torsion O G R (p ^ n) _ (fst_bc R x)).2 (by exact_mod_cast hR)

noncomputable def lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : specO O (DualNumber R) ⟶ torsion G (p ^ n) :=
  (existsUnique_lift hR x).choose

theorem lift_ι {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : lift hR x ≫ torsion.ι G (p ^ n) = bc R x :=
  (existsUnique_lift hR x).choose_spec.1

theorem eq_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) {w : specO O (DualNumber R) ⟶ torsion G (p ^ n)}
    (hw : w ≫ torsion.ι G (p ^ n) = bc R x) : w = lift hR x :=
  (existsUnique_lift hR x).unique hw (lift_ι hR x)

variable (χ : Tv G p)

noncomputable def unitAt {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : DualNumber R :=
  (unitOf (lift hR x ≫ χ.χ n) : DualNumber R)

theorem unitAt_fst {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : (unitAt χ hR x).fst = 1 := by
  set z := ptMap (TrivSqZeroExt.fstHom O R R) ≫ lift hR x with hz
  have h1 : z ≫ torsion.ι G (p ^ n) = 1 := by
    rw [hz, Category.assoc, lift_ι, fst_bc]
  have h2 := χ.isChar n _ z z z (by rw [h1, _root_.mul_one])
  have h3 : unitOf (z ≫ χ.χ n) = 1 := by
    have := congrArg unitOf h2
    rw [unitOf_mul] at this
    exact left_eq_mul.mp this
  have h4 := unitOf_ptMap (TrivSqZeroExt.fstHom O R R) (lift hR x ≫ χ.χ n)
  rw [← Category.assoc, ← hz, h3] at h4
  exact h4.symm

theorem unitAt_map {n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (hR : (p : R) ^ n = 0) (hR' : (p : R') ^ n = 0) (x : LieG G) :
    (unitAt χ hR' x).snd = φ (unitAt χ hR x).snd := by
  have h : ptMap (dualBC φ) ≫ lift hR x = lift hR' x :=
    eq_lift hR' x (by rw [Category.assoc, lift_ι, ptMap_bc])
  rw [unitAt, ← h, Category.assoc, unitOf_ptMap, dualBC_snd, unitAt]

theorem unitAt_le {m n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hm : (p : R) ^ m = 0)
    (hmn : m ≤ n) (hn : (p : R) ^ n = 0) (x : LieG G) : unitAt χ hn x = unitAt χ hm x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hn' : (p : R) ^ n = 0 := pow_eq_zero_of_le hmn hm
    rw [← ih hn', unitAt, unitAt,
      χ.compat n _ (lift hn' x) (lift hn x) (by rw [lift_ι, lift_ι])]

theorem unitAt_mul {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x y z : LieG G) (h : z.1 = x.1 * y.1) :
    (unitAt χ hR z).snd = (unitAt χ hR x).snd + (unitAt χ hR y).snd := by
  have h1 := χ.isChar n _ (lift hR x) (lift hR y) (lift hR z)
    (by rw [lift_ι, lift_ι, lift_ι, bc, bc, bc, h, comp_mul])
  have h2 : unitAt χ hR z = unitAt χ hR x * unitAt χ hR y := by
    rw [unitAt, h1, unitOf_mul, Units.val_mul, unitAt, unitAt]
  rw [h2, DualNumber.snd_mul, unitAt_fst, unitAt_fst]
  ring

theorem unitAt_scale {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (a : O) (x z : LieG G) (h : z.1 = ptMap (dualScale a) ≫ x.1) :
    (unitAt χ hR z).snd = algebraMap O R a * (unitAt χ hR x).snd := by
  have h1 : scale (O := O) (algebraMap O R a) ≫ lift hR x = lift hR z := by
    refine eq_lift hR z ?_
    rw [Category.assoc, lift_ι, bc, bc, h, ← Category.assoc, ← Category.assoc, scale,
      ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 2
    refine AlgHom.ext fun y => ?_
    ext
    · simp [dualBC_fst, dualScale]
    · simp [dualBC_snd, dualScale, Algebra.smul_def]
  rw [unitAt, ← h1, Category.assoc, scale, unitOf_ptMap]
  simp [unitAt, Algebra.smul_def]

theorem pow_quot (n : ℕ) : (p : O ⧸ Ideal.span {(p : O) ^ n}) ^ n = 0 := by
  have : Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p : O) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rwa [map_pow, map_natCast] at this

theorem smod_iff (n : ℕ) (a b : O) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]

theorem eq_of_forall [IsHausdorff (Ideal.span {(p : O)}) O] {a b : O}
    (h : ∀ n, algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b) : a = b := by
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := Ideal.span {(p : O)}) (a - b) fun n => ?_)
  rw [SModEq.zero, ← SModEq.sub_mem, smod_iff]
  exact h n

theorem exists_level (n : ℕ) (x : LieG G) : ∃ a : O, ∀ (R : Type) [CommRing R] [Algebra O R]
    (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (unitAt χ (pow_quot (O := O) n) x).snd
  refine ⟨a, fun R _ _ hR => ?_⟩
  let φ : (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O] R :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId O R) fun c hc => by
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      simp [hR]
  rw [unitAt_map χ φ (pow_quot n) hR, ← ha]
  exact (φ.commutes a).symm

theorem exists_limit [IsPrecomplete (Ideal.span {(p : O)}) O] (x : LieG G) :
    ∃ a : O, ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R]
      (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  choose a ha using fun n => exists_level χ n x
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) a fun {m n} hmn => by
    rw [smod_iff, ha m _ (pow_quot m), ha n _ (pow_eq_zero_of_le hmn (pow_quot m)),
      unitAt_le χ (pow_quot m) hmn]
  refine ⟨L, fun n R _ _ hR => ?_⟩
  have h := hL n
  rw [smod_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq] at h
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
  rw [← ha n R hR, eq_comm, ← sub_eq_zero, ← map_sub, ← hd]
  simp [hR]

theorem isAl_iff (f : LieG G → O) : IsAl χ f ↔ ∀ (x : LieG G) (n : ℕ) (R : Type) [CommRing R]
    [Algebra O R] (hR : (p : R) ^ n = 0), algebraMap O R (f x) = (unitAt χ hR x).snd := by
  constructor
  · intro h x n R _ _ hR
    rw [unitAt, h n R hR x _ (lift_ι hR x), TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]
  · intro h n R _ _ hR x w hw
    rw [eq_lift hR x hw]
    ext
    · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      exact unitAt_fst χ hR x
    · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact (h x n R hR).symm

theorem existsUnique_isAl [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃! f : LieG G → O, f ∈ omega G ∧ IsAl χ f := by
  choose f hf using exists_limit χ
  refine ⟨f, ⟨⟨fun x y h => eq_of_forall (p := p) fun n => ?_,
    fun a x h => eq_of_forall (p := p) fun n => ?_⟩, (isAl_iff χ f).2 hf⟩, fun g hg => ?_⟩
  · rw [map_add (f := _), hf x n _ (pow_quot n), hf y n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_mul χ _ x y _ rfl)
  · rw [map_mul, hf x n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_scale χ _ a x _ rfl)
  · funext x
    refine eq_of_forall (p := p) fun n => ?_
    rw [hf _ n _ (pow_quot n), (isAl_iff χ g).1 hg.2 x n _ (pow_quot n)]

end GlobalTheory.HodgeTateImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsReducedTorsionGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TorsionReduced

theorem isReduced_of_forall_dualNumber (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B]
    (h : ∀ (φ : B →ₐ[F] DualNumber F) (b : B), (φ b).snd = 0) : _root_.IsReduced B := by
  have hs : Subsingleton (KaehlerDifferential F B) := by
    by_contra hne
    have : Nontrivial (KaehlerDifferential F B) := not_subsingleton_iff_nontrivial.mp hne
    obtain ⟨P, hP, -⟩ := (eq_top_or_exists_le_coatom
      (⊥ : Submodule B (KaehlerDifferential F B))).resolve_left bot_ne_top
    have hsimple : IsSimpleModule B (KaehlerDifferential F B ⧸ P) :=
      isSimpleModule_iff_isCoatom.mpr hP
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    letI : Field (B ⧸ m) := Ideal.Quotient.field m
    have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let u : (B ⧸ m) ≃ₐ[F] F := (AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb).symm
    let l : KaehlerDifferential F B →ₗ[B] (B ⧸ m) := e.toLinearMap ∘ₗ P.mkQ
    let D : Derivation F B (B ⧸ m) := l.compDer (KaehlerDifferential.D F B)
    let φ : B →ₐ[F] DualNumber F :=
      { toFun := fun b => TrivSqZeroExt.inl (u (Ideal.Quotient.mk m b)) + TrivSqZeroExt.inr (u (D b))
        map_one' := by ext <;> simp
        map_mul' := fun a b => by
          ext
          · simp
          · simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
        map_zero' := by ext <;> simp
        map_add' := fun a b => by ext <;> simp
        commutes' := fun r => by
          ext
          · simpa [TrivSqZeroExt.algebraMap_eq_inl] using u.commutes r
          · simp [TrivSqZeroExt.algebraMap_eq_inl] }
    have hD : ∀ b, l (KaehlerDifferential.D F B b) = 0 := fun b => by
      have := h φ b
      simpa [φ, D] using this
    have hl : l = 0 := by
      refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation F B) ?_
      rintro _ ⟨b, rfl⟩
      exact hD b
    apply hP.1
    rw [eq_top_iff]
    intro x _
    have := LinearMap.congr_fun hl x
    simpa [l] using this
  have : Algebra.FormallyUnramified F B := ⟨hs⟩
  exact Algebra.FormallyUnramified.isReduced_of_field F B

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem scale_comp_scale (a b : R) :
    TangentPow.scale O a ≫ TangentPow.scale O b = TangentPow.scale O (a * b) := by
  rw [TangentPow.scale, TangentPow.scale, TangentPow.ptMap_comp_ptMap, TangentPow.scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp [_root_.mul_assoc]

theorem eq_const_of_pow_eq_one {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
    {N : ℕ} (hN : IsUnit (N : R)) (y : specO O (DualNumber R) ⟶ G) (hy : y ^ N = 1) :
    y = ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y := by
  set c := ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y with hc
  have h0 : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (TrivSqZeroExt.inlAlgHom O R R) = 𝟙 _ := by
    rw [TangentPow.ptMap_comp_ptMap, ← TangentPow.ptMap_id']
    congr 1
  have h1 : ptMap (TrivSqZeroExt.fstHom O R R) ≫ (y * c⁻¹) = 1 := by
    rw [comp_mul, GrpObj.comp_inv, hc, ← Category.assoc, h0, Category.id_comp, mul_inv_cancel]
  have h2 : c ^ N = 1 := by
    rw [hc, ← MonObj.comp_pow, ← MonObj.comp_pow, hy, comp_one, comp_one]
  have h3 : (y * c⁻¹) ^ N = 1 := by
    rw [mul_pow, inv_pow, hy, h2, inv_one, _root_.mul_one]
  rw [TangentPow.pow_eq_scale_comp h1] at h3
  obtain ⟨a, ha⟩ := hN.exists_left_inv
  have h4 := congrArg (TangentPow.scale O a ≫ ·) h3
  simp only [← Category.assoc, scale_comp_scale, ha, TangentPow.scale_one, Category.id_comp,
    comp_one] at h4
  exact mul_inv_eq_one.mp h4

end GlobalTheory.TorsionReduced

namespace GlobalTheory

theorem isReduced_torsion_geometric_fibre :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G] (N : ℕ), (N : F) ≠ 0 → IsFinite (torsion G N).hom → IsReduced (specO O F ⊗ torsion G N).left := by
  intro O F _ _ _ _ G _ _ N hN hfin
  have : IsAffine (torsion G N).left := isAffine_of_isAffineHom (torsion G N).hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((torsion G N).left.isoSpec.inv ≫ (torsion G N).hom)
  letI : Algebra O Γ((torsion G N).left, ⊤) := ψ.hom.toAlgebra
  let e : specO O Γ((torsion G N).left, ⊤) ≅ torsion G N :=
    Over.isoMk (torsion G N).left.isoSpec.symm hψ.symm
  have h1 : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Module.Finite O Γ((torsion G N).left, ⊤) := (IsFinite.SpecMap_iff ψ).mp h1
  have hred : _root_.IsReduced (TensorProduct O F Γ((torsion G N).left, ⊤)) := by
    refine TorsionReduced.isReduced_of_forall_dualNumber F _ fun φ b => ?_
    let χ : Γ((torsion G N).left, ⊤) →ₐ[O] DualNumber F :=
      (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
    have hy : ((ptMap χ ≫ e.hom) ≫ torsion.ι G N) ^ N = 1 := by
      rw [← MonObj.comp_pow, KernelNoTorsion.torsionι_pow, comp_one]
    have h2 := TorsionReduced.eq_const_of_pow_eq_one hN.isUnit _ hy
    simp only [← Category.assoc] at h2
    have h3 := (cancel_mono e.hom).mp (KernelNoTorsion.torsion_hom_ext h2)
    rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap] at h3
    have h4 := Spec.map_injective (congrArg Over.Hom.left h3)
    have h5 : ∀ a, (χ a).snd = 0 := fun a => by
      have := congrArg TrivSqZeroExt.snd (congrArg (fun f => f.hom a) h4)
      simpa using this
    induction b with
    | add x y hx hy => simp [hx, hy]
    | tmul f a =>
      have : f ⊗ₜ[O] a = f • ((1 : F) ⊗ₜ[O] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, TrivSqZeroExt.snd_smul]
      exact smul_eq_zero_of_right f (h5 a)
  have h4 : IsReduced (Spec (CommRingCat.of (TensorProduct O F Γ((torsion G N).left, ⊤)))) :=
    (affine_isReduced_iff _).mpr hred
  have h3 : IsReduced (specO O F ⊗ specO O Γ((torsion G N).left, ⊤)).left :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O F Γ((torsion G N).left, ⊤)).hom _ h4
  have h0 : IsIso (specO O F ◁ e.inv).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O F ◁ e.inv)))
  exact isReduced_of_isOpenImmersion (specO O F ◁ e.inv).left

end GlobalTheory
end

