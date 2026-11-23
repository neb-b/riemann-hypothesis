module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGalois
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisActionTorsionPairingTameFixedPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

section
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

noncomputable def galSpecHom (τ : Ω ≃ₐ[K] Ω) :
    Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K Ω)) :=
  Over.homMk (spMap τ.toRingEquiv.toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact τ.commutes c)

theorem galSpecHom_one : galSpecHom (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ := by
  ext1
  exact Spec.map_id _

theorem galSpecHom_mul (τ τ' : Ω ≃ₐ[K] Ω) :
    galSpecHom (τ * τ') = galSpecHom τ ≫ galSpecHom τ' := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

noncomputable def galPointAct (A : Over (Sp K)) [MonObj A] :
    (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ A) where
  toFun τ :=
    { toFun := fun x => galSpecHom τ ≫ x
      invFun := fun x => galSpecHom τ⁻¹ ≫ x
      left_inv := fun x => by
        simp only [← Category.assoc, ← galSpecHom_mul, inv_mul_cancel, galSpecHom_one,
          Category.id_comp]
      right_inv := fun x => by
        simp only [← Category.assoc, ← galSpecHom_mul, mul_inv_cancel, galSpecHom_one,
          Category.id_comp]
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  map_one' := by
    ext1 x
    change galSpecHom 1 ≫ x = x
    rw [galSpecHom_one, Category.id_comp]
  map_mul' τ τ' := by
    ext1 x
    change galSpecHom (τ * τ') ≫ x = galSpecHom τ ≫ galSpecHom τ' ≫ x
    rw [galSpecHom_mul, Category.assoc]

theorem galPointAct_left (A : Over (Sp K)) [MonObj A] (τ : Ω ≃ₐ[K] Ω)
    (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) :
    (galPointAct A τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left := rfl

theorem galPointAct_eq_of_agree (A : Over (Sp K)) [MonObj A] (L : IntermediateField K Ω)
    (τ τ' : Ω ≃ₐ[K] Ω) (h : ∀ c ∈ L, τ c = τ' c) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A)
    (y : Sp L ⟶ A.left) (hy : spMap (algebraMap L Ω) ≫ y = x.left) :
    galPointAct A τ x = galPointAct A τ' x := by
  ext1
  rw [galPointAct_left, galPointAct_left, ← hy, ← Category.assoc, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact h c c.2

theorem algEquiv_mem_of_normal (L : IntermediateField K Ω) [Normal K L] (τ : Ω ≃ₐ[K] Ω)
    {c : Ω} (hc : c ∈ L) : τ c ∈ L := by
  have := AlgEquiv.restrictNormal_commutes τ L ⟨c, hc⟩
  change ((τ.restrictNormal L ⟨c, hc⟩ : L) : Ω) = τ c at this
  rw [← this]
  exact Subtype.prop _

theorem pow_tame_relation (L : IntermediateField K Ω) [Normal K L] (σ φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ c ∈ L, φ (σ c) = (σ ^ q) (φ c)) (N : ℕ) :
    ∀ c ∈ L, (φ ^ N * σ) c = (σ ^ q ^ N * φ ^ N) c := by
  have h1 : ∀ (a : ℕ), ∀ c ∈ L, φ ((σ ^ a) c) = (σ ^ (q * a)) (φ c) := by
    intro a
    induction a with
    | zero => intro c _; simp
    | succ a ih =>
      intro c hc
      rw [pow_succ', AlgEquiv.mul_apply, h _ (algEquiv_mem_of_normal L _ hc), ih c hc,
        ← AlgEquiv.mul_apply, ← pow_add, Nat.mul_succ, Nat.add_comm]
  induction N with
  | zero => intro c _; simp
  | succ N ih =>
    intro c hc
    have := ih c hc
    simp only [AlgEquiv.mul_apply] at this
    rw [pow_succ' φ, pow_succ' q]
    simp only [AlgEquiv.mul_apply]
    rw [this, h1 _ _ (algEquiv_mem_of_normal L _ hc)]

end

theorem galois_action_torsion_points : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l q : ℕ), l.Prime → (∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ (σ φ : Ω ≃ₐ[K] Ω) (K' : Type) [Field K'] (j : K' →+* Ω), (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) → (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ j.fieldRange)) → ∃ (e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ) (act : (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), (∀ τ x, (act τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left) ∧ ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ (∀ N n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (act σ x) (act σ y) = e n x y ∧ e n (act (φ ^ N) x) (act (φ ^ N) y) = e n x y ^ (q ^ N)) ∧ (∀ N n x, x ^ l ^ n = 1 → act (φ ^ N) (act σ x) = (act σ)^[q ^ N] (act (φ ^ N) x)) ∧ ∀ n x, x ^ l ^ n = 1 → act σ x = x → ∃ y : Sp K' ⟶ P.A.left, spMap j ≫ y = x.left := by
  intro K _ _ P Ω _ _ _ l q hl hrat σ φ K' _ j hζ hL
  obtain ⟨-, ⟨e, he, hgal⟩, hfield⟩ := _root_.GlobalTheory.torsion_points_galois_module K P Ω l hl
  have hφ : ∀ (m N : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → (φ ^ N) ζ = ζ ^ q ^ N := by
    intro m N ζ h
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, (hζ m ζ h).2, ← pow_mul, pow_succ']
  refine ⟨e, galPointAct P.A, fun τ x => rfl, he, ?_, ?_, ?_⟩
  · intro N n x y hx hy
    obtain ⟨h1, h2⟩ := hgal σ n x y _ _ hx hy (galPointAct_left _ σ x) (galPointAct_left _ σ y)
    obtain ⟨-, h3⟩ := hgal (φ ^ N) n x y _ _ hx hy (galPointAct_left _ _ x)
      (galPointAct_left _ _ y)
    refine ⟨Units.ext ?_, Units.ext ?_⟩
    · rw [h2, (hζ n _ h1).1]
    · rw [h3, hφ n N _ h1, Units.val_pow_eq_pow_val]
  · intro N n x hx
    obtain ⟨L, hfin, hnorm, hp, hpts⟩ := hfield hrat n
    obtain ⟨y, hy⟩ := hpts x hx
    have := galPointAct_eq_of_agree P.A L _ _
      (pow_tame_relation L σ φ q (fun c hc => (hL L hfin hnorm hp c hc).1) N) x y hy
    rw [map_mul, map_mul, map_pow (galPointAct P.A) σ] at this
    rw [← MulAut.mul_apply, this, MulAut.mul_apply]
    generalize galPointAct P.A (φ ^ N) x = z
    generalize q ^ N = k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  · intro n x hx hfix
    obtain ⟨L, hfin, hnorm, hp, hpts⟩ := hfield hrat n
    obtain ⟨E, hE1, hE2, -⟩ := exists_fieldOfValues P.A.left Ω x.left
    have hEL := (hE2 L (algebraMap L Ω)).2 (hpts x hx)
    have hσ := (hE1 σ.toRingEquiv.toRingHom (RingHom.id Ω)).1 (by
      rw [← galPointAct_left, hfix]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ x.left) (Spec.map_id _).symm))
    refine (hE2 K' j).1 fun c hc => ?_
    obtain ⟨d, rfl⟩ := hEL hc
    exact (hL L hfin hnorm hp _ d.2).2 (hσ _ hc)

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExists
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre.CombValue

open GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {x : TFK (R := R) F ⟶ A.A} {e : FrameAt A x}

theorem valIs_comb {J : Type} [Fintype J] {s : J → SecA A F k} {b c : J → F} {t : SecA A F k} (h : IsComb A s b t)
    (hs : ∀ i, ValIs A (s i) x e (c i)) : ValIs A t x e (∑ i, b i * c i) := fun z I hI => by
  have e₀ : SecM.ofSec A.A t = ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  let φ : SecM A.A A.L k (TFK (R := R) F) →+ (TFK (R := R) F).left.presheaf.stalk z :=
    AddMonoidHom.mk' (fun v => ThetaAct.sv v (ptSecT A.A x).left z I) fun a b => ThetaAct.sv_add a b _ z hI
  let ψ : F →+* (TFK (R := R) F).left.presheaf.stalk z := cstH (R := R) z
  have e₁ : ∀ a : F, @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z a) = ψ a := fun a => cst_eq z a
  refine (congrArg φ e₀).trans ((map_sum φ _ _).trans ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e₁, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => (ThetaAct.sv_smul _ _ _ z hI).trans ?_
  rw [ThetaPtMove.ptSecT_fst, map_mul, _root_.mul_assoc, ← e₁, ← e₁]
  exact congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (b i)) * ·) (hs i z I hI)

theorem valIs_smul {t t' : SecA A F k} {a c : F} (h : ∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j)
    (ht : ValIs A t x e c) : ValIs A t' x e (a * c) := by
  have := valIs_comb (J := Unit) (s := fun _ => t) (b := fun _ => a) (c := fun _ => c) (t := t')
    (fun j => (h j).trans (by rw [Fintype.sum_unique])) fun _ => ht
  rwa [Fintype.sum_unique] at this

theorem valIs_unique {t : SecA A F k} {c c' : F} (h : ValIs A t x e c) (h' : ValIs A t x e c') : c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

theorem exists_valIs (hL : Laws) (he : e.IsGen) (t : SecA A F k) : ∃ c, ValIs A t x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

theorem valIs_linear : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x), (∀ (J : Type) [Fintype J] (s : J → SecA A F k) (b c : J → F) (t : SecA A F k), IsComb A s b t → (∀ i, ValIs A (s i) x e (c i)) → ValIs A t x e (∑ i, b i * c i)) ∧ (∀ (t t' : SecA A F k) (a c : F), (∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j) → ValIs A t x e c → ValIs A t' x e (a * c)) ∧ (∀ (t : SecA A F k) c c', ValIs A t x e c → ValIs A t x e c' → c = c') ∧ (e.IsGen → ∀ t : SecA A F k, ∃ c, ValIs A t x e c) :=
  fun hL _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ _ _ _ h hs => valIs_comb h hs, fun _ _ _ _ h ht => valIs_smul h ht,
      fun _ _ _ h h' => valIs_unique h h', fun he t => exists_valIs hL he t⟩

end GlobalTheory.TestFibre.CombValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinCombValueAct
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
noncomputable section
namespace GlobalTheory.ZH.SecComb
open GlobalTheory.ZH.SecValue

theorem pull_liftFun {S : Scheme.{0}} {A T : Over S} [GrpObj A] (ψ : T ⊗ A ⟶ T ⊗ A) (hψ : ψ ≫ fst T A = fst T A)
    {U W : (T ⊗ A).left.Opens} (h : W ≤ ψ.left ⁻¹ᵁ U) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE h).op).hom ((ψ.left.app U).hom (liftFun A U r)) = liftFun A W r := by
  have e : ψ.left ≫ (fst T A).left = (fst T A).left := by rw [← Over.comp_left, hψ]
  have e₁ : ∀ V : (T ⊗ A).left.Opens, liftFun A V r = ((fst T A).left.appLE ⊤ V le_top).hom r := fun _ => rfl
  rw [e₁, e₁]
  refine (congrArg (fun q => q.hom r) (Scheme.Hom.appLE_comp_appLE ψ.left (fst T A).left ⊤ U W le_top h)).trans ?_
  simp only [e]

theorem ring_sum {B B' C I : Type} [CommRing B] [CommRing B'] [CommRing C] [Fintype I] (f' : B' →+* C) (f : B →+* C)
    (u : C) {c s : I → B} {c' s' : I → B'} {t : B} {t' : B'} (ht : t = ∑ l, c l * s l) (ht' : t' = ∑ l, c' l * s' l)
    (hc : ∀ l, f' (c' l) = f (c l)) (h : ∀ l, f' (s' l) = u * f (s l)) : f' t' = u * f t := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ht, ht', map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul, map_mul, h, hc, mul_left_comm]

theorem isTwistPull_sum {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left} (ψ : T ⊗ A ⟶ T ⊗ A)
    (hψ : ψ ≫ fst T A = fst T A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α) {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) {s : I → LB.Sec (LPow A L b T)} {s' : I → LB.Sec (LPow A L a T)}
    {t : LB.Sec (LPow A L b T)} {t' : LB.Sec (LPow A L a T)}
    (ht : ∀ j, t.f j = ∑ l, liftFun A _ (c l) * (s l).f j) (ht' : ∀ j, t'.f j = ∑ l, liftFun A _ (c l) * (s' l).f j)
    (h : ∀ l, IsTwistPull A L ψ m hm a b α (s l) (s' l)) : IsTwistPull A L ψ m hm a b α t t' := fun j =>
  ring_sum _ (RingHom.comp _ _) _ (ht _) (ht' _)
    (fun l => (res_liftHom A _ (c l)).trans (pull_liftFun ψ hψ (chart_le_pull A L ψ m hm j) (c l)).symm) fun l => h l j

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem valM_zero (x) (e : FrAt x) : ValM (0 : SecM A.A A.L k (TFK (R := R) F)) x e 0 := fun z J hJ => by
  have h := ThetaAct.sv_add (0 : SecM A.A A.L k (TFK (R := R) F)) 0 (ptSecT A.A x).left z hJ
  rw [add_zero, left_eq_add] at h
  refine h.trans ?_
  simp only [id, CoefBasic.cst_eq, map_zero]
  exact (zero_mul (M₀ := (TFK (R := R) F).left.presheaf.stalk z) _).symm

theorem valM_sum {x} {e : FrAt x} {J : Type} (s : Finset J)
    {σ : J → SecM A.A A.L k (TFK (R := R) F)} {c : J → F} (h : ∀ l, ValM (σ l) x e (c l)) :
    ValM (∑ l ∈ s, σ l) x e (∑ l ∈ s, c l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valM_zero x e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

theorem exists_valAt (t : SecA A F k) {x} {e : FrAt x} (he : e.IsGen) : ∃ c, ValAt t x e c := by
  obtain ⟨w, hw⟩ := ThetaPtExist.exists_isValueAt A.isLB t x (powFrame A.A A.L x e k) (EvVal.powFrame_isGen A.A A.L x e he k)
  obtain ⟨c, rfl⟩ := kon_surj w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

end

theorem lin_comb_value_act : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (t : SecA A F k) x (e : FrAt x), e.IsGen → ∃! a : F, ValAt t x e a) ∧ ∀ (I : Type) [Fintype I] (c : I → F) (s : I → SecA A F k), (∃ t, IsComb s c t) ∧ ∀ t, IsComb s c t → (∀ x (e : FrAt x) (a : I → F), (∀ i, ValAt (s i) x e (a i)) → ValAt t x e (∑ i, c i * a i)) ∧ ∀ (θ : ThetaGrp A.A A.L k (TFK (R := R) F)) (s' : I → SecA A F k) t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb s' c t' → IsActOf A.A A.L k θ t t' := by
  intro R _ _ A F _ _ k
  refine ⟨fun t x e he => ?_, fun I _ c s => ⟨?_, fun t ht => ⟨fun x e a ha => ?_, fun θ s' t' hs ht' => ?_⟩⟩⟩
  · obtain ⟨a, ha⟩ := exists_valAt t he
    exact ⟨a, ha, fun b hb => ValM.unique (σ := SecM.ofSec A.A t) hb ha⟩
  · exact ⟨SecM.toSec A.A (∑ l, kon R F (c l) • SecM.ofSec A.A (s l)), (isComb_iff _ _ _).2 rfl⟩
  · have h := valM_sum (Finset.univ : Finset I) fun l => ValM.smul (σ := SecM.ofSec A.A (s l)) (ha l) (c l)
    rw [← (isComb_iff _ _ _).1 ht] at h
    exact h
  · exact isTwistPull_sum _ (lift_fst _ _) _ _ _ _ _ (fun l => kon R F (c l)) ht ht' hs

end GlobalTheory.ZH.SecComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetricLiftNormalisedPullbackThetaSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

theorem act_normPull_smul : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th th' : SecA A F 1) (c : F), (∀ j, th.f j = liftFun A.A _ (cF R c) * th'.f j) → ∀ (s₁ σ t : SecA A F (m ^ 2)) (x : TFK (R := R) F ⟶ A.A) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)) (c' : F), x ^ (m ^ 2) = 1 → IsNormPull A ρ m (m ^ 2) th s₁ → SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ → IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ σ → ThC A ρ m th' x t c' → ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j := by
  intro hLL R _ _ _ A F _ _ ρ hρ m hm th th' c hc s₁ σ t x θ c' hx ⟨α, hα, hn, hs₁⟩ hθ hσ
    ⟨α', s₁', θ', hα', hn', hs₁', hθ', ht', _⟩
  have hLaw : Laws := hLL.1
  have hL := A.isLB
  let T := TFK (R := R) F
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨-, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  have f₁ : (mulT A.A T m).left ≫ (fst T A.A).left = (fst T A.A).left := by
    rw [← Over.comp_left, mulT, lift_fst]
  have f₂ : (translT A.A θ.pt).left ≫ (fst T A.A).left = (fst T A.A).left := by
    rw [← Over.comp_left, translT, lift_fst]
  have key : SecM.ofSec A.A σ = cF R c • SecM.ofSec A.A t := ThetaAct.sv_ext hL fun y J hJ => by
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    have a₁ := ThetaLin.sval_of_isTwistPull A.A hσ (𝟙 _) y hJ
    have a₂ := ThetaLin.sval_of_isTwistPull A.A hs₁ (𝟙 _ ≫ (translT A.A θ.pt).left) y hJ
    have a₃ := ThetaPtMove.sv_of_eq_mul hc ((𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mulT A.A T m).left) y hJ
    have b₁ := ThetaLin.sval_of_isTwistPull A.A ht' (𝟙 _) y hJ
    have b₂ := ThetaLin.sval_of_isTwistPull A.A hs₁' (𝟙 _ ≫ (translT A.A θ.pt).left) y hJ
    rw [← val_corr hJ eθ, ← ept, b₂, ← ea _ _ y J hJ] at b₁
    rw [Category.assoc _ (mulT A.A T m).left (fst T A.A).left, f₁, Category.assoc _ _ (fst T A.A).left, f₂] at a₃
    refine a₁.trans (Eq.trans ?_ (congrArg (_ * ·) b₁.symm))
    rw [a₂]
    refine (congrArg (fun q => _ * (_ * q)) a₃).trans ?_
    ring
  exact fun j => congrArg (fun q => q.1 j) key

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemExistsRootOfUnitySumNormAttained
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory

theorem thetaSys_exists_norm_FF_eq :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (B : ℝ), (∀ (t : T) i, ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ ≤ B) → (∃ (t : T) (i : S.J), B ≤ ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖) → ∃ (k : _) (hk : S.FF T c k ∈ S.R), ‖y₀ ⟨S.FF T c k, hk⟩‖ = B := by
  intro o Ω _ _ _ hA S p _ y₀ hy T c B hle ⟨t, i, hge⟩
  have hN := S.N_ge
  have hr := S.r_pos
  have hrN : 2 ≤ S.r * S.N := le_trans hN (Nat.le_mul_of_pos_left _ hr)
  have hn : 1 < (S.r * S.N) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have : Fact (1 < (S.r * S.N) ^ 2) := ⟨hn⟩
  have : IsDomain o := hA.inj.isDomain _
  have : NeZero (S.r * S.N) := ⟨by omega⟩
  have := Fintype.ofFinite T
  have hmem := (thetaSys_FF_mem_finite_perp_proj o Ω S).1 T c
  set E : T → PadicAlgCl p := fun s =>
    ∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev s j, S.ev_mem s j⟩ with hE
  have hval : ∀ k : T → ZMod ((S.r * S.N) ^ 2), y₀ ⟨S.FF T c (i, k), hmem _⟩
      = ∑ s, y₀ (algebraMap o S.R S.ζ) ^ (k s).val * E s := fun k => by
    have : (⟨S.FF T c (i, k), hmem _⟩ : S.R) = ∑ s : T, algebraMap o S.R S.ζ ^ (k s).val *
        ∑ j, algebraMap o S.R (S.proj T c j i) * ⟨S.ev s j, S.ev_mem s j⟩ := by
      apply Subtype.ext
      simp [ThetaSys.FF, finsum_eq_sum_of_fintype]
    rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hE, map_sum]
  have hB : ‖E t‖ = B := le_antisymm (hle t i) hge
  have hB0 : 0 ≤ B := hB ▸ norm_nonneg _
  have h0 : ‖∑ s, E s‖ ≤ B :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun s _ => hle s i
  rcases h0.eq_or_lt with h0 | h0
  · refine ⟨(i, 0), hmem _, ?_⟩
    rw [hval]
    simpa using h0
  · have hu : IsUnit (1 - S.ζ) := by
      obtain ⟨m, hm⟩ : ∃ m, (S.r * S.N) ^ 2 = m + 1 + 1 := ⟨(S.r * S.N) ^ 2 - 2, by omega⟩
      have hp := S.prim
      rw [hm] at hp
      have h1 := hp.prod_one_sub_pow_eq_order
      have h2 : IsUnit ((((S.r * S.N) ^ 2 : ℕ)) : o) := by
        rw [Nat.cast_pow]; exact S.unit.pow _
      rw [hm, Nat.cast_succ, ← h1, Finset.prod_range_succ'] at h2
      simpa using isUnit_of_mul_isUnit_right h2
    have hone : ‖1 - y₀ (algebraMap o S.R S.ζ)‖ = 1 := by
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 := hy (1 - S.ζ)
      have h2 := hy v
      have h3 : ‖y₀ (algebraMap o S.R (1 - S.ζ))‖ * ‖y₀ (algebraMap o S.R v)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, hv, map_one, map_one, norm_one]
      rw [map_sub, map_sub, map_one, map_one] at h1 h3
      refine le_antisymm h1 ?_
      calc (1 : ℝ) = _ := h3.symm
        _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2
    refine ⟨(i, Pi.single t 1), hmem _, ?_⟩
    have hs : ∑ s, y₀ (algebraMap o S.R S.ζ) ^ ((Pi.single t 1 : T → ZMod ((S.r * S.N) ^ 2)) s).val * E s
        = ∑ s, E s + -((1 - y₀ (algebraMap o S.R S.ζ)) * E t) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t),
        ← Finset.add_sum_erase _ E (Finset.mem_univ t),
        Finset.sum_congr rfl (g := E) fun s hs => by
          rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hs), ZMod.val_zero, pow_zero,
            _root_.one_mul]]
      rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      ring
    have hn' : ‖-((1 - y₀ (algebraMap o S.R S.ζ)) * E t)‖ = B := by
      rw [norm_neg, norm_mul, hone, _root_.one_mul, hB]
    rw [hval, hs, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hn']; exact h0.ne),
      hn', max_eq_right h0.le]

end GlobalTheory
end

