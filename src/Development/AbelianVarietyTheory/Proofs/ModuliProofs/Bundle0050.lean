module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsAlongGroupHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.PowLie (sc zeroPt isTangent_iff)
noncomputable section
namespace GlobalTheory.KS.InvHom

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  have h₃ : O₂ ≤ (f ≫ g) ⁻¹ᵁ O₀ := h₂.trans (f.preimage_mono h₁)
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le _ h₃]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem pbT_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) :
    pbT f s (f ⁻¹ᵁ O₀) = (f.app O₀).hom s := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.app_eq_appLE]

theorem constFn_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {Y : Scheme.{0}}
    (q : Y ⟶ Sp R') (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h1 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  refine h1.symm.trans ?_
  exact congrArg (fun t => (q.appLE ⊤ O (fun _ _ => trivial)).hom t) h2.symm

theorem constFn_mul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) (a b : R) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp [constFn]

theorem constFn_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) :
    constFn q O (0 : R) = 0 := by
  simp [constFn]

variable {K : Type} [Field K]

def jA (A : Over (Sp K)) : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ zeroPt K) (𝟙 A)

theorem thick (A : Over (Sp K)) :
    (∀ O : (epsR K ⊗ A).left.Opens, (snd (epsR K) A).left ⁻¹ᵁ ((jA A).left ⁻¹ᵁ O) = O) ∧
    ∀ (O : A.left.Opens) (F : Γ((epsR K ⊗ A).left, (snd (epsR K) A).left ⁻¹ᵁ O)),
      ∃! ab : Γ(A.left, O) × Γ(A.left, O), F = ((snd (epsR K) A).left.app O).hom ab.1 +
        constFn (R := DualNumber K) (fst (epsR K) A).left _ DualNumber.eps *
          ((snd (epsR K) A).left.app O).hom ab.2 := by
  have h := GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left
    (jA A).left (IsPullback.of_hasPullback (epsR K).hom A.hom).flip
    (by rw [← Over.comp_left, jA, lift_snd]; rfl)
    (by
      have : jA A ≫ fst (epsR K) A = toUnit A ≫ zeroPt K := by rw [jA, lift_fst]
      exact congrArg CommaMorphism.left this)
  exact ⟨h.1, h.2.2⟩

abbrev tr {A : Over (Sp K)} [GrpObj A] (v : epsR K ⟶ A) : epsR K ⊗ A ⟶ A :=
  (fst (epsR K) A ≫ v) * snd (epsR K) A

variable {A : Over (Sp K)} [GrpObj A]

theorem tr_preimage {v : epsR K ⟶ A} (hv : IsTangent v) (W : A.left.Opens) :
    (tr v).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  have h : jA A ≫ tr v = 𝟙 A := by
    rw [MonObj.comp_mul, ← Category.assoc, jA, lift_fst, lift_snd, Category.assoc,
      (isTangent_iff v).1 hv]
    exact _root_.one_mul (𝟙 A)
  rw [← (thick A).1 ((tr v).left ⁻¹ᵁ W), ← Scheme.Hom.comp_preimage (jA A).left, ← Over.comp_left, h]
  rfl

theorem pull {v : epsR K ⟶ A} (hv : IsTangent v) {dd} (hd : IsInvDer v dd) {Z : Over (Sp K)}
    (S : Z ⟶ epsR K ⊗ A) (W : A.left.Opens) (f : Γ(A.left, W)) (O : Z.left.Opens)
    (hO : O ≤ (S ≫ snd (epsR K) A).left ⁻¹ᵁ W) :
    pbT (S ≫ tr v).left f O = pbT (S ≫ snd (epsR K) A).left f O +
      constFn (R := DualNumber K) (S ≫ fst (epsR K) A).left O DualNumber.eps *
        pbT (S ≫ snd (epsR K) A).left (dd W f) O := by
  have hO' : O ≤ S.left ⁻¹ᵁ ((snd (epsR K) A).left ⁻¹ᵁ W) := hO
  have h := congrArg (fun s => pbT S.left s O) (hd W f)
  simp only [pbT_add, pbT_mul] at h
  rw [pbT_pbT _ _ (tr_preimage hv W).ge hO', pbT_pbT _ _ le_rfl hO', pbT_pbT _ _ le_rfl hO',
    pbT_constFn _ _ hO'] at h
  exact h

theorem tan_one : IsTangent (1 : epsR K ⟶ A) := by
  rw [isTangent_iff, MonObj.comp_one]
  simp [Hom.one_def]

theorem tan_mul {u u' : epsR K ⟶ A} (hu : IsTangent u) (hu' : IsTangent u') : IsTangent (u * u') := by
  have e : (η[A] : _ ⟶ A) = 1 := by simp [Hom.one_def]
  rw [isTangent_iff] at *
  rw [MonObj.comp_mul, hu, hu', e, _root_.one_mul]

theorem tan_sc {v : epsR K ⟶ A} (hv : IsTangent v) (c : K) : IsTangent (sc c ≫ v) := by
  have e : zeroPt K ≫ sc c = zeroPt K := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [isTangent_iff] at *
  rw [← Category.assoc, e, hv]

theorem inv_one : IsInvDer (1 : epsR K ⟶ A) (fun _ _ => 0) := by
  intro W f
  rw [MonObj.comp_one, _root_.one_mul, pbT_zero, mul_zero, add_zero]

theorem inv_mul {u u' : epsR K ⟶ A} (hu : IsTangent u) (hu' : IsTangent u') {d d'}
    (hd : IsInvDer u d) (hd' : IsInvDer u' d') : IsInvDer (u * u') (fun W f => d W f + d' W f) := by
  intro W f
  have e : (fst (epsR K) A ≫ (u * u')) * snd (epsR K) A = lift (fst _ _) (tr u') ≫ tr u := by
    rw [MonObj.comp_mul, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, _root_.mul_assoc]
  have h := pull hu hd (lift (fst _ _) (tr u')) W f ((snd (epsR K) A).left ⁻¹ᵁ W)
    (by rw [lift_snd]; exact (tr_preimage hu' W).ge)
  rw [lift_snd, lift_fst, hd' W f, hd' W (d W f)] at h
  rw [e, h, pbT_add]
  have h2 : constFn (R := DualNumber K) (fst (epsR K) A).left ((snd (epsR K) A).left ⁻¹ᵁ W) DualNumber.eps *
      constFn (R := DualNumber K) (fst (epsR K) A).left ((snd (epsR K) A).left ⁻¹ᵁ W) DualNumber.eps = 0 := by
    rw [← constFn_mul, DualNumber.eps_mul_eps, constFn_zero]
  linear_combination (pbT (snd (epsR K) A).left (d' W (d W f)) ((snd (epsR K) A).left ⁻¹ᵁ W)) * h2

theorem inv_sc {v : epsR K ⟶ A} (hv : IsTangent v) {d} (hd : IsInvDer v d) (c : K) :
    IsInvDer (sc c ≫ v) (fun W f => constFn A.hom W c * d W f) := by
  intro W f
  have e : (fst (epsR K) A ≫ (sc c ≫ v)) * snd (epsR K) A = (sc c ▷ A) ≫ tr v := by
    rw [MonObj.comp_mul, whiskerRight_snd, whiskerRight_fst_assoc]
  have h := pull hv hd (sc c ▷ A) W f ((snd (epsR K) A).left ⁻¹ᵁ W) (by rw [whiskerRight_snd])
  rw [whiskerRight_snd, whiskerRight_fst] at h
  rw [e, h, pbT_mul, pbT_constFn _ _ le_rfl, ← _root_.mul_assoc]
  congr 2
  have w : (snd (epsR K) A).left ≫ A.hom = (fst (epsR K) A).left ≫ spMap (algebraMap K (DualNumber K)) :=
    (Over.w (snd (epsR K) A)).trans (Over.w (fst (epsR K) A)).symm
  have e2 : epsScaleR c (DualNumber.eps : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) c := by
    ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [w]
  refine (constFn_spMap (epsScaleR c) (fst (epsR K) A).left _ _).trans ?_
  rw [e2]
  refine (constFn_mul _ _ _ _).trans ?_
  congr 1
  exact (constFn_spMap _ _ _ _).symm

theorem inv_prod : ∀ {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (d : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ i, IsTangent (u i)) →
    (∀ i, IsInvDer (u i) (d i)) →
      IsTangent (List.ofFn u).prod ∧ IsInvDer (List.ofFn u).prod (fun W f => ∑ i, d i W f) := by
  intro n
  induction n with
  | zero =>
    intro u d _ _
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨tan_one, inv_one⟩
  | succ n ih =>
    intro u d hu hd
    obtain ⟨h₁, h₂⟩ := ih (fun i => u i.succ) (fun i => d i.succ)
      (fun i => hu i.succ) (fun i => hd i.succ)
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨tan_mul (hu 0) h₁, inv_mul (hu 0) h₁ (hd 0) h₂⟩

theorem inv_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    {d : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hv : ∀ i, IsTangent (v i))
    (hd : ∀ i, IsInvDer (v i) (d i)) (hw : IsLieComb c v w) :
    IsTangent w ∧ IsInvDer w (fun W f => ∑ i, constFn A.hom W (c i) * d i W f) := by
  obtain ⟨u, hu, rfl⟩ := hw
  have e : ∀ i, u i = sc (c i) ≫ v i := fun i => Over.OverMorphism.ext (hu i)
  exact inv_prod u (fun i W f => constFn A.hom W (c i) * d i W f) (fun i => e i ▸ tan_sc (hv i) _)
    (fun i => e i ▸ inv_sc (hv i) (hd i) _)

theorem inv_hom {A₁ : Over (Sp K)} [GrpObj A₁] (f : A₁ ⟶ A) [IsMonHom f] {w : epsR K ⟶ A₁}
    (hw : IsTangent w) (hwf : IsTangent (w ≫ f)) {dw D} (hdw : IsInvDer w dw) (hD : IsInvDer (w ≫ f) D)
    (W : A.left.Opens) (h : Γ(A.left, W)) :
    dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = (f.left.app W).hom (D W h) := by
  have e : (epsR K ◁ f) ≫ tr (w ≫ f) = tr w ≫ f := by
    rw [MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_snd, whiskerLeft_fst_assoc, Category.assoc]
  have h1 := pull hwf hD (epsR K ◁ f) W h ((snd (epsR K) A₁).left ⁻¹ᵁ (f.left ⁻¹ᵁ W))
    (by rw [whiskerLeft_snd]; exact le_rfl)
  rw [e, whiskerLeft_snd, whiskerLeft_fst, Over.comp_left, Over.comp_left,
    ← pbT_pbT _ _ le_rfl (tr_preimage hw _).ge, ← pbT_pbT _ _ le_rfl le_rfl h,
    ← pbT_pbT _ _ le_rfl le_rfl (D W h), pbT_app f.left, pbT_app f.left, pbT_app, pbT_app] at h1
  have h2 := hdw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h)
  rw [pbT_app, pbT_app] at h2
  have := ((thick A₁).2 (f.left ⁻¹ᵁ W) _).unique (y₁ := (_, _)) (y₂ := (_, _)) h2 h1
  exact congrArg Prod.snd this

theorem invDer_along_hom : ∀ (K : Type) [Field K] (A₁ A₀ : Over (Sp K)) [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (w : epsR K ⟶ A₁) (dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)) (c : Fin g → K), IsMonHom f → (∀ a, IsTangent (v a)) → IsTangent w → (∀ a, IsInvDer (v a) (dd a)) → IsInvDer w dw → IsLieComb c v (w ≫ f) → ∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)), dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = ∑ a, constFn A₁.hom _ (c a) * (f.left.app W).hom (dd a W h) := by
  intro K _ A₁ A₀ _ _ f g v dd w dw c hf hv hw hdd hdw hc W h
  obtain ⟨h₁, h₂⟩ := inv_comb hv hdd hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [inv_hom f hw h₁ hdw h₂, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, ← pbT_app f.left (constFn A₀.hom W (c a)), pbT_constFn _ _ le_rfl, Over.w f]

end GlobalTheory.KS.InvHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubalgebraEqTopOfForallPrimeSmulMemSup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.span_range_algebraMap_eq_top_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → Module.Finite R C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Submodule.span B (Set.range (algebraMap R C)) = ⊤ := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcompat _ htame hin
  classical
  let M : Subalgebra B C := Algebra.adjoin B (Set.range (algebraMap R C))
  have hRM : ∀ r : R, algebraMap R C r ∈ M := fun r => Algebra.subset_adjoin ⟨r, rfl⟩
  letI : Algebra R M := ((algebraMap R C).codRestrict M hRM).toAlgebra
  haveI : IsScalarTower R M C := IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite M C := Module.Finite.of_restrictScalars_finite R M C
  have hsmulM : ∀ (m : M) (c : C), m • c = (m : C) * c := fun m c => rfl
  have hsmulB : ∀ (b : B) (c : C), b • c = (algebraMap B M b : C) * c := fun b c => by
    rw [Algebra.smul_def]
    rfl
  let P' : Submodule M C := Submodule.span M {1}
  have hmemP' : ∀ c ∈ M, c ∈ P' := by
    intro c hc
    rw [Submodule.mem_span_singleton]
    exact ⟨⟨c, hc⟩, by rw [hsmulM, _root_.mul_one]⟩
  have hcomp : ∀ (g : Γ) (b : B) (x : C), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hcompat]
  have hin' : ∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ x : C,
      g • x - x ∈ q • (⊤ : Submodule B C) := by
    intro q hq g hg x
    rw [Ideal.smul_top_eq_map]
    exact hin q hq g hg x
  have hloc : ∀ P : Ideal M, P.IsMaximal → (⊤ : Submodule M (C ⧸ P')) ≤ P • ⊤ := by
    intro P hP x _
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective P' x
    haveI : P.IsPrime := hP.isPrime
    have hq : (P.comap (algebraMap B M)).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨s, hs, hsc⟩ := _root_.GlobalTheory.exists_smul_mem_span_invariants_sup Γ B C hcomp _ hq
      (htame _ hq) (hin' _ hq) c
    have hsmall : ∀ y ∈ Submodule.span B {y : C | ∀ g : Γ, g • y = y} ⊔
        (P.comap (algebraMap B M)) • (⊤ : Submodule B C),
        (Submodule.Quotient.mk y : C ⧸ P') ∈ P • (⊤ : Submodule M (C ⧸ P')) := by
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [Submodule.Quotient.mk_add]
      refine add_mem ?_ ?_
      · have h1 : y₁ ∈ Subalgebra.toSubmodule M := by
          refine (Submodule.span_le (p := Subalgebra.toSubmodule M)).mpr ?_ hy₁
          intro z hz
          obtain ⟨r, rfl⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := Γ) z hz
          exact hRM r
        rw [(Submodule.Quotient.mk_eq_zero P').mpr (hmemP' _ h1)]
        exact zero_mem _
      · refine Submodule.smul_induction_on
          (p := fun y => (Submodule.Quotient.mk y : C ⧸ P') ∈ P • (⊤ : Submodule M (C ⧸ P'))) hy₂ ?_ ?_
        · intro b hb z _
          rw [show b • z = (algebraMap B M b) • z by rw [hsmulM, hsmulB],
            Submodule.Quotient.mk_smul]
          exact Submodule.smul_mem_smul hb trivial
        · intro z w hz hw
          simp only [Submodule.Quotient.mk_add]
          exact add_mem hz hw
    have hσ : algebraMap B M s ∉ P := hs
    obtain ⟨u, i, hi, hui⟩ := hP.exists_inv hσ
    have hx : (Submodule.Quotient.mk c : C ⧸ P') =
        u • (Submodule.Quotient.mk (s • c) : C ⧸ P') + i • Submodule.Quotient.mk c := by
      rw [show s • c = (algebraMap B M s) • c by rw [hsmulM, hsmulB], Submodule.Quotient.mk_smul,
        smul_smul, ← add_smul, hui, one_smul]
    rw [hx]
    exact add_mem (Submodule.smul_mem _ _ (hsmall _ hsc)) (Submodule.smul_mem_smul hi trivial)
  have hann : Module.annihilator M (C ⧸ P') = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P
      (⊤ : Submodule M (C ⧸ P')) Module.Finite.fg_top (hloc P hP)
    have hrP : r ∈ P := hle (Module.mem_annihilator.mpr fun n => hr n trivial)
    have h1 : (1 : M) ∈ P := by simpa using P.sub_mem hrP hr1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  refine eq_top_iff.mpr fun c _ => ?_
  have h1 : (1 : M) ∈ Module.annihilator M (C ⧸ P') := by
    rw [hann]
    exact Submodule.mem_top
  have hc0 : (Submodule.Quotient.mk c : C ⧸ P') = 0 := by
    have h := Module.mem_annihilator.mp h1 (Submodule.Quotient.mk c)
    rwa [one_smul] at h
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero P').mp hc0)
  rw [hsmulM, _root_.mul_one] at hm
  have hcM : c ∈ Subalgebra.toSubmodule M := hm ▸ m.2
  rw [Algebra.adjoin_eq_span] at hcM
  refine Submodule.span_mono ?_ hcM
  intro z hz
  have hcl : Submonoid.closure (Set.range (algebraMap R C)) ≤
      (algebraMap R C).rangeS.toSubmonoid :=
    Submonoid.closure_le.mpr fun w ⟨r, hr⟩ => ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hcl hz
  exact ⟨r, hr⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointFixedOfGenericSectionsFixed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem comp_eq_of_extending_section {X U W G T : Scheme.{0}} [IsReduced X] (j : U ⟶ X)
    [IsDominant j] (g : G ⟶ X) [IsSeparated g] (a : W ⟶ G) [IsOpenImmersion (a ≫ g)]
    (s : U ⟶ G) (hs : pullback.fst (a ≫ g) j ≫ a = pullback.snd (a ≫ g) j ≫ s)
    (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G ⟶ G) (hr : r₀ ≫ j = j ≫ r) (hφ : φ ≫ g = g ≫ r)
    (hsφ : s ≫ φ = r₀ ≫ s) (w : T ⟶ W) (hw : w ≫ (a ≫ g) ≫ r = w ≫ a ≫ g) :
    w ≫ a ≫ φ = w ≫ a := by
  have key : ∀ {V : Scheme.{0}} (v : V ⟶ W) (u : V ⟶ U), v ≫ a ≫ g = u ≫ j → v ≫ a = u ≫ s := by
    intro V v u h
    have := congrArg (pullback.lift v u h ≫ ·) hs
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  let f₁ := pullback.fst (a ≫ g) ((a ≫ g) ≫ r)
  let f₂ := pullback.snd (a ≫ g) ((a ≫ g) ≫ r)
  have hc : f₁ ≫ a ≫ g = f₂ ≫ (a ≫ g) ≫ r := pullback.condition
  let t := f₂ ≫ a ≫ g
  have : IsOpenImmersion t := inferInstance
  have : IsReduced (pullback (a ≫ g) ((a ≫ g) ≫ r)) := isReduced_of_isOpenImmersion t
  have := isDominant_pullback_fst_of_isOpenMap j t t.isOpenEmbedding.isOpenMap
  have hd : pullback.fst t j ≫ f₂ ≫ a ≫ g = pullback.snd t j ≫ j := pullback.condition
  have he : f₂ ≫ a ≫ φ = f₁ ≫ a := by
    refine ext_of_isDominant_of_isSeparated g ?_ (pullback.fst t j) ?_
    · simp only [Category.assoc, hφ, hc]
    · have h₁ := key (pullback.fst t j ≫ f₂) (pullback.snd t j) ((Category.assoc _ _ _).trans hd)
      have h₂ := key (pullback.fst t j ≫ f₁) (pullback.snd t j ≫ r₀) (by
        simp only [Category.assoc, hc, hr, reassoc_of% hd])
      simp only [Category.assoc] at h₁ h₂
      rw [h₂, reassoc_of% h₁, hsφ]
  have := congrArg (pullback.lift w w hw.symm ≫ ·) he
  simpa only [f₁, f₂, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this

theorem torsion_point_fixed_of_generic_sections_fixed : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G : Over X) [GrpObj G] (n : ℕ) (I : Type) [Finite I] (σ : I → (Over.mk j ⟶ G)) (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G.left ⟶ G.left), IsSemiAbelian G → IsUnit (n : Γ(X, ⊤)) → (∀ i, σ i ^ n = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Over.mk (u ≫ j) ⟶ G), y ^ n = 1 → ∃ i, y.left = u ≫ (σ i).left) → r₀ ≫ j = j ≫ r → IsIso r → IsGrpPullback G G r φ → (∀ i, (σ i).left ≫ φ = r₀ ≫ (σ i).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (y : Over.mk x ⟶ G), x ≫ r = x → y ^ n = 1 → y.left ≫ φ = y.left := by
  intro X U _ j hN hj₁ hj₂ hj₃ hj₄ G _ n I _ σ r r₀ φ hG hn hσ hgeo hr _ hφ hσφ k _ _ x y hx hy
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := IsNormalScheme.of_pred hN
  have hex : ∀ {T : Over X} (z : T ⟶ G), z ^ n = 1 →
      ∃ z' : T ⟶ torsion G n, z' ≫ torsion.ι G n = z := fun z hz =>
    ⟨pullback.lift z (toUnit _) (by rw [GrpTangent.comp_mulN, hz, Hom.one_def]),
      pullback.lift_fst _ _ _⟩
  have hι : torsion.ι G n ^ n = 1 := by
    rw [← GrpTangent.comp_mulN, Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (toUnit_unique _ _))
  have hcl : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 X))
    exact IsClosedImmersion.of_comp _ G.hom
  have : IsClosedImmersion (torsion.ι G n).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (GrpTangent.isPullback_torsion G n).flip hcl
  have hsep : IsSeparated (torsion G n).hom := by
    rw [← Over.w (torsion.ι G n)]; infer_instance
  choose τ hτ using fun i => hex (σ i) (hσ i)
  have hτ' : ∀ i, (τ i).left ≫ (torsion.ι G n).left = (σ i).left := fun i =>
    congrArg Over.Hom.left (hτ i)
  obtain ⟨y', rfl⟩ := hex y hy
  obtain ⟨i, W, hyW, hW, he⟩ := exists_opens_isOpenImmersion_extending_section X U j hN hj₁ hj₂
    hj₃ hj₄ _ (torsion G n).hom I (fun i => (τ i).left) (GrpTangent.etale_torsion G hn) hsep
    (fun i => Over.w (τ i)) (fun k _ _ u z hz => by
      obtain ⟨i, hi⟩ := hgeo k u (Over.homMk z hz ≫ torsion.ι G n)
        (by rw [← comp_pow, hι, comp_one])
      refine ⟨i, ?_⟩
      rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτ']
      exact hi) (y'.left (IsLocalRing.closedPoint k))
  have hrange : Set.range y'.left ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum k) z (IsLocalRing.closedPoint k)]
    exact hyW
  have hw := IsOpenImmersion.lift_fac W.ι y'.left hrange
  have hq : (W.ι ≫ (torsion.ι G n).left) ≫ G.hom = W.ι ≫ (torsion G n).hom := by
    rw [Category.assoc, Over.w]
  have : IsOpenImmersion ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) := hq ▸ hW
  have hyx : y'.left ≫ (torsion G n).hom = x := Over.w y'
  have := comp_eq_of_extending_section j G.hom (W.ι ≫ (torsion.ι G n).left) (σ i).left (by
      have h := congrArg (pullback.lift (pullback.fst ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) j)
        (pullback.snd _ j) (by rw [← hq]; exact pullback.condition) ≫ · ≫ (torsion.ι G n).left) he
      simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc, hτ'] using h)
    r r₀ φ hr hφ.1.w (hσφ i) (IsOpenImmersion.lift W.ι y'.left hrange)
    (by rw [hq, Category.assoc, reassoc_of% hw, reassoc_of% hw, reassoc_of% hyx, hyx, hx])
  simpa only [Category.assoc, reassoc_of% hw, Over.comp_left] using this

end GlobalTheory
end

