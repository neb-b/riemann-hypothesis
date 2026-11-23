module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEven
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauDiagEqUnitMulPsiSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

theorem left_comp_hom_unit {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))}
    (s : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) : s.left ≫ B.hom = 𝟙 _ :=
  Over.w s

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R :=
  Over.w (toUnit (TK R))

theorem tau_diag_eq_unit_mul_psi_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (hT : D.TauBimult) (hE : D.PsiEven) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : TopGood D.P z J) (y : D.X) :
    ∃ u : Rˣ, val (D.tau y y) (𝟙 _) z J = uK R z u * val (D.psi y) (𝟙 _) z J ^ 2 := by
  have hG := hJ.1
  set P : D.X → ((TK R).left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J with hPdef
  have hP : ∀ χ, val (D.psi χ) (𝟙 _) z J = P χ := fun _ => rfl
  set rg := val D.rigK (𝟙 _) z J with hrgdef

  have h1 : ∀ a b, val (D.tau a b) (𝟙 _) z J = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * rg⁻¹ := by
    intro a b
    unfold DegPre.tau
    rw [val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]

  obtain ⟨r, hr⟩ : ∃ u : Rˣ, rg = uK R z u := by
    rw [hrgdef]
    unfold DegPre.rigK
    rw [val_pull hG, Category.id_comp, toUnit_TK_left]
    have e : jK R = jK R ≫ (𝟙 (Spec (CommRingCat.of R)) : Spec (CommRingCat.of R) ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) :=
      (Category.comp_id _).symm
    rw [e]
    exact val_section_unit D.P z J hJ D.rig _ (fun _ => by
      rw [Category.id_comp]; exact left_comp_hom_unit (η[D.P.A]))

  set C : D.X → D.X → D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun a a' b => val D.cub.t (D.pt3 a a' b) z J with hCdef
  have h2 : ∀ a a' b, val (D.tau (a + a') b) (𝟙 _) z J * C a a' b =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J := by
    intro a a' b
    have := (val_mul hG _ _ _).symm.trans ((val_corr hG (hT a a' b) (𝟙 _)).trans (val_mul hG _ _ _))
    have hp : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J = C a a' b :=
      (val_pull hG D.cub.t (D.pt3 a a' b) (𝟙 _)).trans (by rw [Category.id_comp])
    exact (congrArg (fun x => val (D.tau (a + a') b) (𝟙 _) z J * x) hp).symm.trans this
  have hC : ∀ a a' b, ∃ u : Rˣ, C a a' b = uK R z u := by
    intro a a' b
    have e : D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
      unfold DegPre.pt3
      rw [← comp_lift, ← comp_lift, Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.cub.t (D.pt3 a a' b) z J = uK R z u
    rw [e]
    exact val_section_unit D.P z J hJ D.cub.t _ (fun k => by
      rw [← Over.comp_left]; exact left_comp_hom_unit _)

  set S : D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun χ => val D.sym (D.xK χ) z J with hSdef
  have h3 : ∀ χ, P (-χ) * S χ = P χ := by
    intro χ
    have := (val_mul hG _ _ _).symm.trans (val_corr hG (hE χ) (𝟙 _))
    rw [val_pull hG, Category.id_comp] at this
    exact this
  have hS : ∀ χ, ∃ u : Rˣ, S χ = uK R z u := by
    intro χ
    have e : D.xK χ = jK R ≫ (D.c χ).left := by
      show (toUnit (TK R) ≫ D.c χ).left = _
      rw [Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.sym (D.xK χ) z J = uK R z u
    rw [e]
    refine val_section_unit D.P z J hJ D.sym _ (fun k => ?_)
    fin_cases k
    · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = 𝟙 _
      rw [← Over.comp_left]; exact left_comp_hom_unit _
    · show ((D.c χ).left ≫ 𝟙 D.P.A.left) ≫ D.P.A.hom = 𝟙 _
      rw [Category.comp_id]; exact left_comp_hom_unit _

  obtain ⟨c0, hc0⟩ := hC 0 0 0
  obtain ⟨c1, hc1⟩ := hC y (-y) y
  obtain ⟨s, hs⟩ := hS y
  have e0 := h2 0 0 0
  simp only [h1, add_zero] at e0

  have hP0 : P 0 = (C 0 0 0 * rg)⁻¹ := by
    have : C 0 0 0 = P 0 * (P 0)⁻¹ * (P 0)⁻¹ * rg⁻¹ := mul_left_cancel e0
    rw [this]; group
  have e1 := h2 y (-y) y
  simp only [h1, add_neg_cancel, zero_add, neg_add_cancel] at e1
  have hPm : P (-y) = P y * (S y)⁻¹ := by rw [← h3 y]; group
  rw [hPm, hP0] at e1
  refine ⟨(c0 * r) ^ 2 * c1 * s⁻¹, ?_⟩
  rw [h1, map_mul, map_mul, map_inv, map_pow, map_mul, ← hc0, ← hc1, ← hs, ← hr, hP y]

  rw [eq_mul_inv_of_mul_eq e1.symm]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegeneration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def precompHom {C : Type*} [Category C] [CartesianMonoidalCategory C] {M X Y : C} [MonObj M] (f : X ⟶ Y) :
    (Y ⟶ M) →* (X ⟶ M) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' g₁ g₂ := MonObj.comp_mul f g₁ g₂

def degCHom {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) :
    D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) where
  toFun x := Additive.ofMul (D.c x)
  map_zero' := by
    have h : D.c (0 + 0) = D.c 0 * D.c 0 := D.c_add 0 0
    rw [add_zero] at h
    have h1 : D.c 0 = 1 := by simpa using h.symm
    rw [h1]; rfl
  map_add' x y := by rw [D.c_add]; rfl

theorem degC_sum_zsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (n : Fin r → ℤ) (x : Fin r → D.X) :
    D.c (∑ j, n j • x j) = ∏ j, D.c (x j) ^ n j := by
  have h := congrArg Additive.toMul (map_sum (degCHom D) (fun j => n j • x j) Finset.univ)
  rw [toMul_sum] at h
  refine h.trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zsmul, toMul_zsmul]
  rfl

theorem Tens.c_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (s : SymUnit r), letI := T.mod s; ∀ (a : TensO s) (y : D'.X),
    D'.c (a • y) = D'.c y ≫ T.act (TensO.mat s a) := by
  intro R _ _ D D' r W T s
  letI := T.mod s
  intro a y
  refine Fan.IsLimit.hom_ext T.lim _ _ fun i => ?_
  show D'.c (a • y) ≫ T.pr i = (D'.c y ≫ T.act (TensO.mat s a)) ≫ T.pr i
  rw [T.c_pr, Category.assoc, T.act_pr, Tens.xe_smul, degC_sum_zsmul D]
  have h := map_prod (precompHom (M := D.P.A) (D'.c y)) (fun j => T.pr j ^ TensO.mat s a i j) Finset.univ
  refine Eq.trans ?_ h.symm
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow]
  show _ = (D'.c y ≫ T.pr j) ^ _
  rw [T.c_pr]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataCubicalStructureValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensCube

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def tensHom (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : D'.P.A ⟶ D.P.A :=
  ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2

theorem tensφ_eq (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : tensφ T.pr k = (tensHom T k).left := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m <;> rfl

theorem tensHom_mul (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))}
    (a b : Z ⟶ D'.P.A) : (a * b) ≫ tensHom T k = (a ≫ tensHom T k) * (b ≫ tensHom T k) := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  haveI := T.pr_hom i
  haveI := T.pr_hom j
  fin_cases m
  · show (a * b) ≫ (T.pr i * T.pr j) = (a ≫ (T.pr i * T.pr j)) * (b ≫ (T.pr i * T.pr j))
    rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _
  · show (a * b) ≫ T.pr i = (a ≫ T.pr i) * (b ≫ T.pr i)
    exact MonObj.mul_comp _ _ _
  · show (a * b) ≫ T.pr j = (a ≫ T.pr j) * (b ≫ T.pr j)
    exact MonObj.mul_comp _ _ _
  · show (a * b) ≫ (1 : D'.P.A ⟶ D.P.A) = (a ≫ 1) * (b ≫ 1)
    rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, _root_.mul_one]

def tensHomH (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) (Z : Over (Spec (CommRingCat.of R))) :
    (Z ⟶ D'.P.A) →* (Z ⟶ D.P.A) :=
  MonoidHom.mk' (· ≫ tensHom T k) (tensHom_mul T k)

def cubeρ (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : (G3 D'.P.A).left ⟶ (G3 D.P.A).left :=
  (lift (x3 D'.P.A 0 ≫ tensHom T k) (lift (x3 D'.P.A 1 ≫ tensHom T k) (x3 D'.P.A 2 ≫ tensHom T k))).left

theorem cube_comm (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) (I : thK) :
    thφ D'.P.A (x3 D'.P.A) I ≫ tensφ T.pr k = cubeρ T k ≫ thφ D.P.A (x3 D.P.A) I := by
  rw [tensφ_eq]
  show (psum D'.P.A (x3 D'.P.A) I.down).left ≫ (tensHom T k).left = _ ≫ (psum D.P.A (x3 D.P.A) I.down).left
  rw [cubeρ, ← Over.comp_left, ← Over.comp_left]
  congr 1
  show tensHomH T k _ (psum D'.P.A (x3 D'.P.A) I.down) = preHom _ (psum D.P.A (x3 D.P.A) I.down)
  rw [psum_hom, psum_hom]
  congr 1
  funext n
  fin_cases n <;> simp [x3, tensHomH, preHom]

end GlobalTheory.Mum.TensCube

namespace GlobalTheory.Mum.TensCube

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem one_tensHom (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))} :
    (1 : Z ⟶ D'.P.A) ≫ tensHom T k = 1 := map_one (tensHomH T k Z)

theorem lift_cubeρ (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))}
    (a b c : Z ⟶ D'.P.A) : (lift a (lift b c)).left ≫ cubeρ T k =
      (lift (a ≫ tensHom T k) (lift (b ≫ tensHom T k) (c ≫ tensHom T k))).left := by
  rw [cubeρ, ← Over.comp_left]
  congr 1
  simp [x3]

theorem cube_tens (hG : GlobalFnsSt) (T : Tens D D' W) {Z : Scheme.{0}} (q : Z ⟶ (G3 D'.P.A).left) (z : Z)
    {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    (∏ a : thK.{0}, GlobalTheory.TensEven.bwE T.w (q ≫ thφ D'.P.A (x3 D'.P.A) a) z
        (fun i => J ((q ≫ thφ D'.P.A (x3 D'.P.A) a) ≫ tensφ T.pr i)) (J' (q ≫ thφ D'.P.A (x3 D'.P.A) a)) ^ thε a) *
      val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t q z J' =
      ∏ k, val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (q ≫ cubeρ T k) z J ^ tensε W k := by
  have hA := D'.P.isAb
  have he : (lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left ≫
      (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w _
  refine GlobalTheory.TensEven.box_uniqueE (pr := tensφ T.pr) (εp := tensε W) D.P.isLB D'.P.isLB T.w T.w_gen
    (φ' := thφ D'.P.A (x3 D'.P.A)) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) (ρ := cubeρ T)
    (fun k I => cube_comm T k I) D'.cub.isGen D.cub.isGen _ _ he
    (surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)) (fun y I I' hI hI' => ?_) Z q z J J' hJ hJ'
  have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
    (fun ψ => GlobalTheory.TensEven.bwE T.w ψ y (fun i => I (ψ ≫ tensφ T.pr i)) (I' ψ))
  simp only [_root_.mul_one, mul_inv_cancel, inv_mul_cancel] at p
  have c' : val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t
      (lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left y I' = 1 :=
    (isCub_cubV D'.cub hI').face 1 1
  have c : ∀ k, val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
      ((lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left ≫ cubeρ T k) y I = 1 := fun k => by
    rw [lift_cubeρ, one_tensHom]
    exact (isCub_cubV D.cub hI).face 1 1
  refine (congrArg₂ (· * ·) p c').trans ?_
  simp only [c, one_zpow, Finset.prod_const_one]
  group

end GlobalTheory.Mum.TensCube

namespace GlobalTheory.Mum.TensCube

theorem alg {U : Type} [CommGroup U] (Θ P hxyu hxy hxu hyu hx hy hu h1 : U)
    (key : hxyu * hxy⁻¹ * hxu⁻¹ * hyu⁻¹ * hx * hy * hu * h1⁻¹ * Θ = P) :
    Θ * hxyu * hx * hy * hu = P * hxy * hxu * hyu * h1 := by
  subst key
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem theta_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ x y u, (N'.θ x y u : F) * wv T ν ν' (x * y * u) * wv T ν ν' x * wv T ν ν' y * wv T ν ν' u =
    ((∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j) (cmp T ν ν' u i * cmp T ν ν' u j) /
        (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) * N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j : Fˣ) : F) *
      wv T ν ν' (x * y) * wv T ν ν' (x * u) * wv T ν ν' (y * u) * wv T ν ν' 1 := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' x y u
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ : Good D.toPre.P.L z ν.J := fun ψ => ν.good ψ trivial
  have hJ' : Good D'.toPre.P.L z ν'.J := fun ψ => ν'.good ψ trivial
  let h : ((TF (R := R) F).left ⟶ D'.toPre.P.A.left) → ((Sp F).presheaf.stalk z)ˣ := fun ψ =>
    GlobalTheory.TensEven.bwE T.w ψ z (fun i => ν.J (ψ ≫ tensφ T.pr i)) (ν'.J ψ)
  let τ : Fˣ →* ((Sp F).presheaf.stalk z)ˣ := Units.map (toStk z).toMonoidHom
  have vw : ∀ a, toStk z (wv T ν ν' a) = (h (ν'.eA a).left).val := fun a =>
    toStk_valF (ν'.eA a).left (LB.wchart D.toPre.P.L (tensφ T.pr) (fun k => ν.J ((ν'.eA a).left ≫ tensφ T.pr k)) ⊓
      D'.toPre.P.L.U (ν'.J (ν'.eA a).left)) z ⟨hJ.mem (tensφ T.pr) _, hJ' _⟩ _
  have vθ' : toStk z (N'.θ x y u : F) =
      (cubV D'.toPre.cub (T := TF (R := R) F) z ν'.J (ν'.eA x) (ν'.eA y) (ν'.eA u)).val :=
    (congrArg (toStk z) (ν'.θ_eq x y u)).trans (toStk_valF _ _ z (hJ'.mem _ _) _)
  have tθ : ∀ a b c, τ (N.θ a b c) = cubV D.toPre.cub (T := TF (R := R) F) z ν.J (ν.eA a) (ν.eA b) (ν.eA c) := fun a b c =>
    Units.ext ((Units.coe_map _ _).trans ((congrArg (toStk z) (ν.θ_eq a b c)).trans (toStk_valF _ _ z (hJ.mem _ _) _)))
  have ecmp : ∀ a j, ν.eA (cmp T ν ν' a j) = ν'.eA a ≫ T.pr j := fun a j => ν.eA.apply_symm_apply _
  have key := cube_tens GlobalTheory.globalFns_holds T (Z := Sp F) (lift (ν'.eA x) (lift (ν'.eA y) (ν'.eA u))).left z hJ hJ'
  have key' := (congrArg₂ (· * ·) (prod_cub (ν'.eA x) (ν'.eA y) (ν'.eA u) h) rfl).symm.trans key
  have c1 := (isCub_cubV D.toPre.cub hJ).face (1 : TF (R := R) F ⟶ D.toPre.P.A) 1
  have hP : τ (∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j)
      (cmp T ν ν' u i * cmp T ν ν' u j) / (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) *
        N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j) =
      ∏ k, val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        ((lift (ν'.eA x) (lift (ν'.eA y) (ν'.eA u))).left ≫ cubeρ T k) z ν.J ^ tensε W k := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.prod_univ_four]
    simp only [lift_cubeρ]
    haveI := T.pr_hom i
    haveI := T.pr_hom j
    have m0 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 0) = ν.eA (cmp T ν ν' a i * cmp T ν ν' a j) := fun a => by
      rw [map_mul, ecmp, ecmp]; exact MonObj.comp_mul _ _ _
    have m1 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 1) = ν.eA (cmp T ν ν' a i) := fun a => (ecmp a i).symm
    have m2 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 2) = ν.eA (cmp T ν ν' a j) := fun a => (ecmp a j).symm
    have m3 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 3) = 1 := fun a => MonObj.comp_one _
    change _ = cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ * cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ *
      cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ * cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _
    rw [m0, m0, m0, m1, m1, m1, m2, m2, m2, m3, m3, m3, c1, ← tθ, ← tθ, ← tθ, map_zpow, map_div, map_mul]
    simp only [tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, one_zpow, _root_.mul_one, zpow_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_div, ofMul_one]
    module
  rw [← hP] at key'
  apply (toStk z).injective
  have eq1 : toStk z (((∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j)
      (cmp T ν ν' u i * cmp T ν ν' u j) / (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) *
        N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j : Fˣ) : F)) = (τ _).val :=
    (Units.coe_map _ _).symm
  simp only [map_mul, vw, vθ', eq1, map_one]
  simp only [← Units.val_mul]
  congr 1
  refine alg _ _ _ _ _ _ _ _ _ _ ?_
  exact key'

end GlobalTheory.Mum.TensCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationPsiCoordEqUnitMulProd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensPsiCoord

open GlobalTheory.PsiTauCoordRel GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  intro R _ _ _ Q D' r W pr xe hT y k hk x hx
  obtain ⟨-, -, -, w, -, hpsi⟩ := hT
  haveI : IsProper D'.P.A.hom := D'.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ D'.P.isLB D'.P.A.hom
  obtain ⟨J, hJ, hc⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ Q.M.isLB Q.B.hom
  have E := hpsi y ξ J J' hJ hJ'

  obtain ⟨j, h, hj, rfl⟩ := hx
  obtain ⟨u₁, g₁⟩ := val_psi_chart D' ξ hJ' hc' y j hj (h trivial)
  have eP := gm_genVal ξ (D'.psi y) j h

  obtain ⟨u₂, e₂⟩ : ∃ u : Rˣ, (gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y)))).val =
      GlobalTheory.PeriodBalance.cst ξ u := by
    refine GlobalTheory.PeriodBalance.unit_gm' ξ (D'.c y).left _ (And.intro (Set.mem_iInter.2 fun I => ?_) ?_) _
    · obtain ⟨q, hq⟩ : ∃ q : D'.P.A ⟶ Q.B, tensφ pr I = q.left := by
        obtain ⟨⟨a, b⟩, c⟩ := I
        fin_cases c <;> exact ⟨_, rfl⟩
      have := hc ((D'.c y).left ≫ tensφ pr I) (by
        rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
      rw [← Category.assoc] at this
      exact this
    · exact hc' _ (Over.w _)

  have hv : ∀ i j, ∃ v : Rˣ, val (Q.tau (xe y i) (xe y j)) (𝟙 _) ξ J =
      GlobalTheory.TauShift.kK ξ (k i j) * GlobalTheory.TauShift.cK ξ v := by
    intro i j
    obtain ⟨u, -, hu⟩ := hk i j
    obtain ⟨v, hv⟩ : ∃ v : Rˣ, val u (jK R ≫ 𝟙 _) ξ J = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom v := by
      refine val_int ξ hc u (𝟙 _) fun l => ?_
      obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B,
          GlobalTheory.PolDeg.lamPts (Q.c (xe y i)) (Q.c (xe y j)) l = q.left := by
        fin_cases l <;> exact ⟨_, rfl⟩
      rw [Category.id_comp, hq, Over.w q]; rfl
    refine ⟨v, (hu ξ J hJ).trans (congrArg₂ (· * ·) ?_ ?_)⟩
    · have := GlobalTheory.RefTauCoord.gm_unitOn (RingHom.id (FractionRing R)) ξ (k i j)
      rw [show spMap (RingHom.id (FractionRing R)) = 𝟙 _ by simp] at this
      exact Units.ext this
    · rw [toUnit_left, ← Category.comp_id (jK R)]; exact hv
  choose v hv using hv
  have hc2 : ∀ z : Rˣ, GlobalTheory.TauShift.kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom z) =
      GlobalTheory.TauShift.cK ξ z := fun z => Units.ext rfl
  refine ⟨u₁⁻¹ * u₂ * ∏ i, ∏ j, v i j ^ W i j, Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_⟩
  change GlobalTheory.TauShift.kK ξ _ = GlobalTheory.TauShift.kK ξ _
  have eP' : gm (𝟙 _) ξ (LB.wchart D'.P.L (fun _ : PUnit => D'.xK y) j) ((D'.psi y).s j) =
      GlobalTheory.TauShift.kK ξ (genVal (D'.psi y) j h) := Units.ext eP
  have e₂' : gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) = GlobalTheory.TauShift.cK ξ u₂ :=
    Units.ext e₂
  have G := g₁.symm.trans (E.trans (by rw [e₂']))
  rw [eP'] at G
  simp only [hv] at G
  simp only [map_mul, map_inv, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib, hc2] at G ⊢
  have G' := congrArg ((GlobalTheory.TauShift.cK ξ u₁)⁻¹ * ·) G
  simp only [inv_mul_cancel_left] at G'
  rw [G']
  ac_rfl

end GlobalTheory.TensPsiCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' vs → v' = u' := by
  intro F _ N N' r W φ e wv hT v' u' vs hv hu
  obtain ⟨-, hφ, -, -, -, hw, -⟩ := hT
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hu1, hu2⟩ := hu
  have hb : v'.b = u'.b := hφ.1 (funext fun j => (hv1 j).trans (hu1 j).symm)
  refine NumD.Gt.ext hb (funext fun χ' => ?_)
  have h1 := hv2 χ'
  have h2 := hu2 χ'
  rw [← hb] at h2
  have hne : wv (N'.c χ') * wv v'.b ≠ 0 := mul_ne_zero (hw _) (hw _)
  apply Units.ext
  apply mul_right_cancel₀ hne
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, h1, h2]

end GlobalTheory.Mum.TensTor
end

