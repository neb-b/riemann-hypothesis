module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsBoxSec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]

def kv (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def gsH (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

theorem gs_eqH (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) : gs f y U a = gsH f y U h a :=
  gs_eq f y U h a

theorem gs_sum' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {N : Type} (s : Finset N) (a : N → Γ(X, U)) :
    gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eqH f y U h, map_sum]

theorem gs_prod' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {N : Type} (s : Finset N) (a : N → Γ(X, U)) :
    gs f y U (∏ i ∈ s, a i) = ∏ i ∈ s, gs f y U (a i) := by
  simp only [gs_eqH f y U h, map_prod]

theorem gs_zero' (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 0 = 0 := by
  simp only [gs_eqH f y U h, map_zero]

theorem gs_cst (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (cst p U a) = kv (r ≫ p) z a :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))

theorem gen_ratio {K : Type} [Field K] {M : LB X} (hM : M.IsLB) {N : Type} [Fintype N] {φ : N → (Y ⟶ X)} {ε : N → ℤ}
    (p : Y ⟶ Sp K) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : K, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u' r z J).val = kv (r ≫ p) z c * (val u r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u' (LB.invGen M _ _ u)) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu' (DVR.invGen_isGen _ _ _ _ hu))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have key : (val u' r z J * (val u r z J)⁻¹).val = kv (r ≫ p) z c := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem gs_sec_pw {L : LB X} {m : ℤ} (s : LB.Sec (pw L m)) (r : Z ⟶ X) (z : Z) (i j : L.ι) (hi : r z ∈ L.U i)
    (hj : r z ∈ L.U j) :
    gs r z (L.U i) (s.f i) = (gm r z (L.U i ⊓ L.U j) (L.g i j) ^ m).val * gs r z (L.U j) (s.f j) := by
  have hm : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  refine (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat i j)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))
  exact (gs_unit r z _ hm _).trans (congrArg Units.val (map_zpow _ _ _))

theorem exists_boxSec {L : LB X} {m : ℤ} {N I : Type} [Fintype N] [Fintype I] (φ : N → (Y ⟶ X)) (p : Y ⟶ Sp R)
    (q : I → R) (s : I → N → LB.Sec (pw L m)) : ∃ S : LB.Sec (LB.LinComb L φ (fun _ => m)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (S.f j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
  obtain ⟨F, hF⟩ : ∃ F : ∀ j : N → L.ι, Γ(Y, LB.wchart L φ j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (F j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
    refine ⟨fun j => ∑ a, cst p _ (q a) * ∏ c, rs Y (LB.wchart_le L φ j c) (((φ c).app (L.U (j c))).hom ((s a c).f (j c))),
      fun Z r z j h => ?_⟩
    rw [gs_sum' r z _ h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gs_mul r z _ h, gs_cst p r z _ h, gs_prod' r z _ h]
    refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
    exact (gs_res r z _ h _).trans (gs_pull r (φ c) z _ (LB.wchart_le L φ j c h) _)
  refine ⟨⟨F, fun j j' => fn_ext fun y hy => ?_⟩, hF⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hF _ (𝟙 Y) y j hy.1).trans (Eq.trans ?_ (congrArg _ (hF _ (𝟙 Y) y j' hy.2)).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_left_comm, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
  exact gs_sec_pw _ _ y _ _ (LB.wchart_le L φ j c hy.1) (LB.wchart_le L φ j' c hy.2)

theorem exists_perm (hN : Out.MulNSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hm : (m : K) ≠ 0) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (ξ ξ' : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A))
    (h : Function.Injective ξ) (h' : Function.Injective ξ')
    (e : ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1)
    (e' : ∀ I c, (List.ofFn fun r : Fin 4 => ξ' I r ^ al r c).prod = 1) :
    ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ P.g)), ξ' = fun I => ξ (σ I) := by
  haveI := P.isAb.comm
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp K := Spec.map (CommRingCat.ofHom (algebraMap K k))
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => hm (by rw [h0, Nat.cast_zero])
  have hc := GlobalTheory.card_ker_int_matrix_four (Over.mk t ⟶ P.A) m (2 * P.g) al hm1 hal (fun n hn => by
    have hn0 : (n : K) ≠ 0 := fun h0 => hm (by obtain ⟨d, rfl⟩ := hn; rw [Nat.cast_mul, h0, zero_mul])
    refine (hN _ P n (Nat.pos_of_ne_zero fun h0 => hn0 (by rw [h0, Nat.cast_zero]))).2.2.2.2 k t ?_
    rw [← map_natCast (algebraMap K k)]
    exact (map_ne_zero _).2 hn0)
  have hepi : Epi t := by
    haveI : Flat t := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    haveI : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective t
  let f : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (Over.mk t ⟶ P.A) := preHom (toUnit (Over.mk t))
  have hf : Function.Injective f := fun a b hab => by
    have h1 : (toUnit (Over.mk t)).left ≫ a.left = (toUnit (Over.mk t)).left ≫ b.left := congrArg (·.left) hab
    have h2 : (toUnit (Over.mk t)).left = t := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk t)))
    haveI : Epi (toUnit (Over.mk t)).left := h2 ▸ hepi
    exact Over.OverMorphism.ext ((cancel_epi _).1 h1)
  have bij : ∀ (ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A)), Function.Injective ζ →
      (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) →
      ∃ E : (Fin 4 → Fin (m ^ P.g)) ≃ {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1},
        ∀ I r, (E I).1 r = f (ζ I r) := by
    intro ζ hζ he
    let g : (Fin 4 → Fin (m ^ P.g)) → {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      fun I => ⟨fun r => f (ζ I r), fun c => by
        have := congrArg f (he I c)
        rw [List.prod_ofFn, map_prod, map_one] at this
        simpa only [map_zpow] using this⟩
    have hg : Function.Injective g := fun I I' hI => hζ (funext fun r => hf (congrFun (congrArg Subtype.val hI) r))
    haveI : Finite {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    refine ⟨Equiv.ofBijective g (hg.bijective_of_nat_card_le ?_), fun _ _ => rfl⟩
    rw [hc, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    exact le_of_eq (by congr 1; ring)
  obtain ⟨E, hE⟩ := bij ξ h e
  obtain ⟨E', hE'⟩ := bij ξ' h' e'
  refine ⟨E'.trans E.symm, funext fun I => funext fun r => hf ?_⟩
  rw [← hE, ← hE']
  simp

theorem det_calc {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (Q Q' T : Matrix I I K)
    (c rho rho' : I → K) (n : ℕ) (hQ : ∀ a b, Q (σ a) b = c a * ∑ d, Q' a d * T b d)
    (hr : ∀ a, rho' a = c a ^ n * rho (σ a)) :
    Q.det ^ (2 * n) * ∏ a, rho a ^ 2 = (Q'.det ^ (2 * n) * ∏ a, rho' a ^ 2) * T.det ^ (2 * n) := by
  have h1 : Q.submatrix σ id = Matrix.diagonal c * (Q' * T.transpose) := by
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    exact hQ a b
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_permute, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h2
  have h3 : Q.det ^ 2 = ((∏ a, c a) * (Q'.det * T.det)) ^ 2 := by
    rw [← h2, mul_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h4 : ∏ a, rho' a ^ 2 = (∏ a, c a) ^ (2 * n) * ∏ a, rho a ^ 2 := by
    rw [← Equiv.prod_comp σ (fun a => rho a ^ 2), ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => by rw [hr]; ring
  rw [h4, pow_mul, h3]
  ring

end GlobalTheory.BoxDetUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDominantComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyCx


open TensorProduct in
theorem exists_dominant_component :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (g : R →+* ℂ), ∃ (E : Type) (_ : CommRing E) (_ : IsDomain E) (_ : Algebra ℂ E) (ρ : R →+* E) (e : E →ₐ[ℂ] ℂ), Algebra.FiniteType ℂ E ∧ Function.Injective ρ ∧ e.toRingHom.comp ρ = g := by
  intro R _ _ _ g
  letI : Algebra R (ℂ ⊗[ℤ] R) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat R (ℂ ⊗[ℤ] R) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight ℤ R ℂ).symm.toLinearEquiv
  let e₀ : (ℂ ⊗[ℤ] R) →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) g.toIntAlgHom (fun _ _ => Commute.all _ _)
  have he : ∀ r : R, e₀ (algebraMap R (ℂ ⊗[ℤ] R) r) = g r := by
    intro r
    change e₀ (1 ⊗ₜ r) = g r
    simp [e₀]
  let Q : Ideal (ℂ ⊗[ℤ] R) := RingHom.ker e₀.toRingHom
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hqQ, hq, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal R)) (q := Q.under R) Q bot_le
  refine ⟨(ℂ ⊗[ℤ] R) ⧸ q, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk q).comp (algebraMap R _),
    Ideal.Quotient.liftₐ q e₀ (fun a ha => hqQ ha), inferInstance, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : r ∈ q.under R :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    rw [← hlo.over] at h1
    exact h1
  · ext r
    exact he r

end GlobalTheory.KeyCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEnumKerTransposeSimilitudePoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_enum_ker_transpose : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x, (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) ∧ (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) := by
  intro laws K _ _ x m al hm hal
  classical
  haveI := x.P.isAb.comm
  haveI := x.P.isAb.smooth
  haveI : LocallyOfFiniteType x.P.A.hom := inferInstance
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm Nat.cast_zero
  letI : CommGroup (Pt x) := Hom.commGroup
  have hG : ∀ k : ℕ, k ∣ m → Nat.card {y : Pt x // y ^ k = 1} = k ^ (2 * x.P.g) := by
    rintro k ⟨l, rfl⟩
    have hk : (k : K) ≠ 0 := fun h => hm (by rw [Nat.cast_mul, h, zero_mul])
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])
    exact (laws.mulN (Sp K) x.P k hk1).2.2.2.2 K (𝟙 _) hk
  have hcard := GlobalTheory.card_ker_int_matrix_four (Pt x) m (2 * x.P.g) al (Nat.pos_of_ne_zero hm0) hal hG
  have hfin : Finite {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)
  have hc : Nat.card (Fin 4 → Fin (m ^ x.P.g)) =
      Nat.card {ξ : Fin 4 → Pt x // ∀ c, ∏ r', ξ r' ^ al r' c = 1} := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    congr 1
    ring
  obtain ⟨e⟩ := Finite.card_eq.mp hc
  refine ⟨fun I => (e I).1, fun I I' hI p => ?_, fun I c => ?_⟩
  · by_contra hne
    push_neg at hne
    refine hI (e.injective (Subtype.ext (funext fun r => ?_)))
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst hp
    exact Over.OverMorphism.ext
      (ext_of_apply_closedPoint_eq x.P.A.hom (Over.w _) (Over.w _) (hne r))
  · rw [List.prod_ofFn]
    exact (e I).2 c

end GlobalTheory.KeyKa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

theorem _root_.GlobalTheory.KeyTf.exists_finiteType_subring_adjoin :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (F : Finset S), Algebra.FiniteType ℤ R₀ →
      ∃ R₁ : Subring S, R₀ ≤ R₁ ∧ (F : Set S) ⊆ R₁ ∧ Algebra.FiniteType ℤ R₁ := by
  intro S _ R₀ F hR₀
  classical
  obtain ⟨s, hs⟩ := hR₀.out
  let T : Finset S := s.image (Subtype.val) ∪ F
  refine ⟨(Algebra.adjoin ℤ (T : Set S)).toSubring, ?_, ?_, ?_⟩
  · intro x hx
    have hmem : (⟨x, hx⟩ : R₀) ∈ Algebra.adjoin ℤ (s : Set R₀) := hs ▸ Algebra.mem_top
    have h2 : x ∈ (Algebra.adjoin ℤ (s : Set R₀)).map R₀.subtype.toIntAlgHom :=
      Subalgebra.mem_map.2 ⟨_, hmem, rfl⟩
    rw [← Algebra.adjoin_image] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)
  · intro x hx
    exact Algebra.subset_adjoin (Finset.mem_union_right _ hx)
  · exact (Subalgebra.fg_iff_finiteType _).1 ⟨T, rfl⟩

end GlobalTheory.KeyTf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilUnit

section Rep

variable {X Y Y' : Scheme.{0}} (L : LB X)

def IsVal (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ y J, Good L y J → val t (𝟙 Y) y J = v y J

variable {L} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
  {v v' : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ}

theorem IsVal.pull {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (r : Y ⟶ Y') :
    IsVal L (fun _ _ h => ∏ k, h (r ≫ φ k) ^ ε k) (fun y J => val t r y J) :=
  ⟨K, inferInstance, _, ε, LB.pullGen L φ ε t r, DVR.pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun y J hJ => by rw [val_pull hJ, Category.id_comp]⟩

theorem IsVal.one : IsVal L (Y := Y) (fun _ _ _ => 1) (fun _ _ => 1) :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L, fun i j => by
    refine (map_one _).trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _), fun _ _ _ => Fintype.prod_empty _, fun _ _ _ => val_one _⟩

theorem IsVal.mul (a : IsVal L F v) (b : IsVal L F' v') :
    IsVal L (fun U _ h => F U h * F' U h) (fun y J => v y J * v' y J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := b
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hF U h) (hF' U h))
  · rw [val_mul hJ, hv y J hJ, hv' y J hJ]

theorem IsVal.inv (a : IsVal L F v) : IsVal L (fun U _ h => (F U h)⁻¹) (fun y J => (v y J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · rw [val_inv, hv y J hJ]

theorem IsVal.pow (a : IsVal L F v) (n : ℕ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using IsVal.one
  | succ n ih => simpa only [pow_succ] using ih.mul a

theorem IsVal.zpow (a : IsVal L F v) (n : ℤ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [zpow_natCast] using a.pow k
  · simpa only [zpow_neg, zpow_natCast] using (a.pow k).inv

theorem IsVal.prod {I : Type} {G : I → ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
    {u : I → ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ} (a : ∀ i, IsVal L (G i) (u i)) (s : Finset I) :
    IsVal L (fun U _ h => ∏ i ∈ s, G i U h) (fun y J => ∏ i ∈ s, u i y J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using IsVal.one
  | insert d s hd ih => simpa only [Finset.prod_insert hd] using (a d).mul ih

theorem IsVal.exists_unit (hL : L.IsLB) (a : IsVal L F v)
    (h1 : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = 1) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ y J, Good L y J → (v y J).val = gs (𝟙 Y) y ⊤ u.val := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨t', -, hv'⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => ((hF U h).trans (h1 U h)).trans (Fintype.prod_empty _).symm) t ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t'.s PEmpty.elim), fun y J hJ => ?_⟩
  rw [← hv y J hJ, ← hv' _ _ y J hJ, val_of t' _ y J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res _ y le trivial _)).symm.trans (gs_unit _ y ⊤ trivial _).symm

end Rep

theorem pow_eq_one_of_similitude {A I : Type} [CommGroup A] [Fintype I] [DecidableEq I] (m : ℕ) (hm : m ≠ 0)
    (al : Matrix I I ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix I I ℤ)) (ξ : I → A)
    (hk : ∀ c, ∏ r, ξ r ^ al r c = 1) (r : I) : ξ r ^ m = 1 := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  have hd : al.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hal
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
    exact pow_ne_zero _ hm' this.symm
  have h2 : al * al.transpose = (m : ℤ) • (1 : Matrix I I ℤ) := by
    have e : (al * al.transpose) * al = ((m : ℤ) • (1 : Matrix I I ℤ)) * al := by
      rw [Matrix.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have e' := congrArg (· * al.adjugate) e
    simp only [Matrix.mul_assoc (_ : Matrix I I ℤ) al al.adjugate, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e'
    exact smul_right_injective _ hd e'
  have e : ∏ c, (∏ r', ξ r' ^ al r' c) ^ al r c = ξ r ^ m := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    have : ∀ r', ∏ c, ξ r' ^ (al r' c * al r c) = ξ r' ^ (if r' = r then (m : ℤ) else 0) := fun r' => by
      have := congrFun (congrFun h2 r') r
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, _root_.mul_one, mul_zero] at this
      rw [← this]
      exact (map_prod (zpowersHom A (ξ r')) (fun c => Multiplicative.ofAdd (al r' c * al r c)) Finset.univ).symm
    simp only [this, pow_ite, zpow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true, zpow_natCast]
  rw [← e]
  simp only [hk, one_zpow, Finset.prod_const_one]

theorem exists_normalising_unit : ∀ (R : Type) [CommRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x) (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2])) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), m ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → mu.IsGen → w.IsGen → ∃ rho : Rˣ, ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → (val w (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ r).left p J).val = gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ rho) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val := by
  intro R _ x m al ξ mu w hm hal hk hmu hw
  haveI := x.P.isAb.comm
  have hξ : ∀ r, ξ r ^ m = 1 := pow_eq_one_of_similitude m hm al hal ξ fun c => by
    simpa only [List.prod_ofFn] using hk c
  have e₁ : ∀ c, eSec (Out.powObj x.P.A 4) ≫ (Out.powPr x.P.A c).left = eSec x.P.A := fun c =>
    congrArg CommaMorphism.left (IsMonHom.one_hom (Out.powPr x.P.A c))
  have e₂ : ∀ r, eSec (Out.powObj x.P.A 4) ≫ (alMap x al r (ξ r)).left = (ξ r).left := fun r => by
    have h1 : ∀ c, η[Out.powObj x.P.A 4] ≫ Out.powPr x.P.A c = 1 := fun c => by
      rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    have : η[Out.powObj x.P.A 4] ≫ alMap x al r (ξ r) = ξ r := by
      simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
        MonObj.comp_one, h1, one_zpow, _root_.one_mul]
      rw [← Category.assoc, toUnit_unique (η[_] ≫ toUnit _) (𝟙 _), Category.id_comp]
    exact congrArg CommaMorphism.left this
  have e₃ : ∀ r, (ξ r).left ≫ ((𝟙 x.P.A) ^ m).left = eSec x.P.A := fun r => by
    have : ξ r ≫ (𝟙 x.P.A) ^ m = η[x.P.A] := by
      rw [MonObj.comp_pow, Category.comp_id, hξ, Hom.one_def, toUnit_unit, Category.id_comp]
    exact congrArg CommaMorphism.left this
  obtain ⟨u, hu⟩ := ((((IsVal.pull hw (eSec (Out.powObj x.P.A 4))).pow (m ^ 2)).mul
    (IsVal.prod (fun r => IsVal.pull hmu (ξ r).left) Finset.univ)).mul
    ((IsVal.pull x.rig_gen (𝟙 _)).zpow (4 - 4 * (m : ℤ) ^ 3)).inv).exists_unit x.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e₁, e₂, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₃, Category.comp_id, Category.id_comp, Fintype.prod_unique, zpow_one,
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_unique, Finset.prod_zpow]
      generalize h (eSec x.P.A) = a
      generalize (∏ r, h (ξ r).left) = b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one]
      module)
  let E := RingEquiv.ofBijective _ (cst_bijective (𝟙 (Sp R)) (W := ⊤) rfl)
  refine ⟨Units.map E.symm.toMonoidHom u, fun p J hJ => ?_⟩
  have e : cst (𝟙 (Sp R)) ⊤ (Units.map E.symm.toMonoidHom u : Rˣ) = u.val := E.apply_symm_apply u.val
  rw [e]
  have := hu p J hJ
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul] at this
  exact this

end GlobalTheory.SimilUnit
end
end

