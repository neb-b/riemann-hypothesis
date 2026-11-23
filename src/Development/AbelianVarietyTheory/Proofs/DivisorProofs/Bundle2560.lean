module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorTensorPowerCorrespondsFormalSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.TensRos
open GlobalTheory.TensBal GlobalTheory.TensAct
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecHom_add (T : Tens D D' W) (u v : Vec r) : vecHom T (u + v) = vecHom T u * vecHom T v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (T : Tens D D' W) : vecHom T 0 = 1 := by
  simp [vecHom]

theorem prod_single {G : Type} [CommGroup G] (f : Fin r → G) (i : Fin r) :
    ∏ k, f k ^ (Pi.single i (1 : ℤ) : Fin r → ℤ) k = f i := by
  rw [Fintype.prod_eq_single i (fun k hk => by rw [Pi.single_eq_of_ne hk, zpow_zero])]
  rw [Pi.single_eq_same, zpow_one]

theorem vecHom_xv (T : Tens D D' W) (i : Fin r) : vecHom T (xv i) = fst D'.P.A D'.P.A ≫ T.pr i := by
  simp only [vecHom, xv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  exact prod_single _ i

theorem vecHom_zv (T : Tens D D' W) (i : Fin r) : vecHom T (zv i) = snd D'.P.A D'.P.A ≫ T.pr i := by
  simp only [vecHom, zv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  exact prod_single _ i

theorem vecHom_axv (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom T (axv A i) = fst D'.P.A D'.P.A ≫ matAct T A ≫ T.pr i := by
  simp only [vecHom, axv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  rw [matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  exact Finset.prod_congr rfl fun k _ => (GrpObj.comp_zpow _ _ _).symm

theorem vecHom_azv (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom T (azv A i) = snd D'.P.A D'.P.A ≫ matAct T A ≫ T.pr i := by
  simp only [vecHom, azv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  rw [matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  exact Finset.prod_congr rfl fun k _ => (GrpObj.comp_zpow _ _ _).symm

theorem ros_pr (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) :
    ∃ q : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, rosatiφ D'.P.A (matAct T A) (matAct T A') a = q.left ∧
      ∀ k, q ≫ T.pr k = vecHom T (rosVec A A' a k) := by
  have hp := T.pr_hom
  fin_cases a
  · refine ⟨(fst D'.P.A D'.P.A ≫ matAct T A) * snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (axv A k + zv k)
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_axv, vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A ≫ matAct T A, rfl, fun k => ?_⟩
    show _ = vecHom T (axv A k)
    rw [vecHom_axv, Category.assoc]
  · refine ⟨snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (zv k)
    rw [vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A * (snd D'.P.A D'.P.A ≫ matAct T A'), rfl, fun k => ?_⟩
    show _ = vecHom T (xv k + azv A' k)
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_xv, vecHom_azv]
  · refine ⟨fst D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (xv k)
    rw [vecHom_xv]
  · refine ⟨snd D'.P.A D'.P.A ≫ matAct T A', rfl, fun k => ?_⟩
    show _ = vecHom T (azv A' k)
    rw [vecHom_azv, Category.assoc]

def lamV (u v : Vec r) : Fin 4 → Vec r := ![u + v, u, v, 0]

theorem ros_lam (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i j : Fin r) (s : Fin 4) :
    rosatiφ D'.P.A (matAct T A) (matAct T A') a ≫ GlobalTheory.PolDeg.lamPts (T.pr i) (T.pr j) s =
      (vecHom T (lamV (rosVec A A' a i) (rosVec A A' a j) s)).left := by
  obtain ⟨q, hq, hk⟩ := ros_pr T A A' a
  rw [hq]
  fin_cases s
  · show q.left ≫ (T.pr i * T.pr j).left = _
    rw [← Over.comp_left, MonObj.comp_mul, hk, hk]
    show _ = (vecHom T (rosVec A A' a i + rosVec A A' a j)).left
    rw [vecHom_add]
  · show q.left ≫ (T.pr i).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (T.pr j).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (1 : D'.P.A ⟶ D.P.A).left = _
    rw [← Over.comp_left, MonObj.comp_one]
    show _ = (vecHom T 0).left
    rw [vecHom_zero]
theorem formEq_sig (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) :
    FormEq (fun p : Fin 6 × ((Fin r × Fin r) × Fin 4) =>
        rosatiφ D'.P.A (matAct T A) (matAct T A') p.1 ≫ tensφ T.pr p.2)
      (fun p => rosatiε p.1 * tensε W p.2)
      (fun v : (sig W A A').support => (vecHom T v.1).left) (fun v => sig W A A' v.1) := by
  intro U _ h
  let H : Vec r → Additive U := fun v => Additive.ofMul (h (vecHom T v).left)
  let F : (Vec r →₀ ℤ) →+ Additive U := Finsupp.liftAddHom fun v => zmultiplesHom (Additive U) (H v)
  have hF1 : ∀ x, F (Finsupp.single x 1) = H x := fun x => by
    simp only [F, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]
  have hlam : ∀ u v, F (lam u v) = ∑ s : Fin 4, Oε s • H (lamV u v s) := fun u v => by
    simp only [lam, map_add (f := _), map_sub, hF1, Fin.sum_univ_four]
    simp [Oε, lamV]
    abel
  have hR : Additive.ofMul (∏ v : (sig W A A').support, h (vecHom T v.1).left ^ sig W A A' v.1) =
      F (sig W A A') := by
    rw [ofMul_prod]
    simp only [ofMul_zpow]
    rw [Finset.sum_coe_sort (sig W A A').support (fun v => sig W A A' v • H v)]
    simp only [F, Finsupp.liftAddHom_apply, zmultiplesHom_apply]
    rfl
  apply Additive.ofMul.injective
  rw [hR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ofMul_prod, ofMul_zpow, sig, map_sum, map_zsmul, hlam]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (rosatiε a * (W i j * Oε s)) • Additive.ofMul (h (rosatiφ D'.P.A (matAct T A) (matAct T A') a ≫
    GlobalTheory.PolDeg.lamPts (T.pr i) (T.pr j) s)) = _
  rw [ros_lam, ← _root_.mul_assoc, mul_smul]

theorem ros_sig : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A')) rosatiε)), u'.IsGen → LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L) → ∀ (Ξ : LB.Gen (LB.LinComb D.P.L (fun v : (GlobalTheory.TensBal.sig W A A').support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => GlobalTheory.TensBal.sig W A A' v.1))), Ξ.IsGen → (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ y y' : D'.X, (∏ a, GlobalTheory.TensBal.isoV T.w z J J' (D'.pt2 y y' ≫ rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') a) ^ rosatiε a) * val u' (D'.pt2 y y') z J' = val Ξ (D'.pt2 y y') z J := by
  intro R _ _ D D' r W T A A' u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  haveI := matAct_hom T A
  haveI := matAct_hom T A'
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : zero2 D'.P.A ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D'.P.A] η[D'.P.A])
  refine _root_.GlobalTheory.TensBalUniq.iso_unique D.P.isLB D'.P.isLB T.w T.w_gen (formEq_sig T A A') hu' hΞ _ (zero2 D'.P.A) he sj
    (fun s I I' hI hI' => ?_) _ (D'.pt2 y y') z J J' hJ hJ'
  have o : (η[D'.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = 1 := by simp [Hom.one_def]
  have p := prod_ros (matAct T A) (matAct T A') η[D'.P.A] η[D'.P.A] (fun q => isoV T.w s I I' q)
  rw [IsMonHom.one_hom, IsMonHom.one_hom, show η[D'.P.A] * η[D'.P.A] = η[D'.P.A] by rw [o, _root_.mul_one]] at p
  have v' := val_corr hI' hn' (𝟙 _)
  rw [val_pull hI', Category.id_comp, val_one] at v'
  rw [hΞ0 s I hI]
  refine (congrArg₂ (· * ·) p v').trans (by simp)

end GlobalTheory.TensRos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarsInt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
open GlobalTheory.UU GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit

noncomputable section

namespace GlobalTheory.MumInt

theorem bal_part {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (k : D.X → (FractionRing R)ˣ) (hk : PsiScal D ga k) {a a' : D.P.A ⟶ D.P.A} {h h' : D.X →+ D.X}
    (hE : EndData D a a' h h') (y w : D.X) :
    ∃ u ∈ unitsK R, k (h y + w) * k y * k (h' w) = u * (k (y + h' w) * k (h y) * k w) := by
  obtain ⟨ha, ha', hr, -, -, hb⟩ := hE
  obtain ⟨t, ht, t₀⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB a a' hr
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPos.exists_int D.P z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hψ : ∀ χ, val (D.psi χ) (𝟙 _) z J = E (k χ) * val (ga χ) (toUnit (TK R)).left z J := fun χ =>
    Units.ext (((hk χ).2 (TK R) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have mg : ∀ χ, val (ga χ) (toUnit (TK R)).left z J ∈ unitsS z := fun χ => GlobalTheory.Mum.TensPos.val_mem D.P z iJ _ _ _
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hb t ht t₀ y w) (𝟙 _))
  have ep : 𝟙 _ ≫ D.pt2 y w = (toUnit (TK R)).left ≫ (lift (D.c y) (D.c w)).left := by
    rw [Category.id_comp, ← Over.comp_left, comp_lift]; rfl
  have mt : val t (𝟙 _ ≫ D.pt2 y w) z J ∈ unitsS z := by
    rw [ep, ← val_pull hJ]
    refine GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ _
    have hφ : rosatiφ D.P.A a a' i ≫ D.P.A.hom = (D.P.A ⊗ D.P.A).hom := by
      fin_cases i <;> exact Over.w _
    rw [Category.assoc, hφ]
    exact Over.w _
  rw [vτ, vτ] at e
  simp only [hψ] at e
  generalize val t (𝟙 _ ≫ D.pt2 y w) z J = v at e mt
  refine ⟨k (h y + w) * k y * k (h' w) * (k (y + h' w) * k (h y) * k w)⁻¹, GlobalTheory.Mum.TensPol.mem_unitsK z ?_,
    by rw [inv_mul_cancel_right]⟩
  have : E (k (h y + w) * k y * k (h' w) * (k (y + h' w) * k (h y) * k w)⁻¹) =
      val (ga (y + h' w)) (toUnit (TK R)).left z J * val (ga (h y)) (toUnit (TK R)).left z J *
        val (ga w) (toUnit (TK R)).left z J * (val (ga (h y + w)) (toUnit (TK R)).left z J *
        val (ga y) (toUnit (TK R)).left z J * val (ga (h' w)) (toUnit (TK R)).left z J * v)⁻¹ := by
    simp only [map_mul, map_inv]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  exact this ▸ mul_mem (mul_mem (mul_mem (mg _) (mg _)) (mg _))
    (inv_mem (mul_mem (mul_mem (mul_mem (mg _) (mg _)) (mg _)) mt))

theorem scalars_int {R : Type} [CommRing R] [IsDomain R] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (k : X → (FractionRing R)ˣ) (h h' : X →+ X) (N : ℕ)
    (hn : ∀ x, ∃ u ∈ unitsK R, k (-x) = u * k x)
    (hc : ∀ x y w, ∃ u ∈ unitsK R, k (x + y + w) * k x * k y * k w = u * (k (x + y) * k (x + w) * k (y + w)))
    (hi : ∀ x, x ≠ 0 → ∃ s : R, (k x : FractionRing R) = algebraMap R _ s)
    (hb : ∀ y w, ∃ u ∈ unitsK R, k (h y + w) * k y * k (h' w) = u * (k (y + h' w) * k (h y) * k w))
    (hP : ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 →
      (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) →
      (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) →
      (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
        algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) →
      ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y)) (y : X) :
    (∃ s : R, (k y : FractionRing R) = algebraMap R _ s) ∧
      ∃ ρ : R, ((k y ^ N * (k (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ ρ * k y := by
  obtain ⟨B, hB⟩ := exists_exact (unitsK R) k hn hc
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  have eκ : ∀ x, k x = u x * κ x := eu
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κ0 : κ 0 = 1 := by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add (f := _), LinearMap.add_apply]
    abel
  have κi : ∀ x, ∃ s : R, (κ x : FractionRing R) = algebraMap R _ s := fun x => by
    by_cases hx : x = 0
    · exact ⟨1, by rw [hx, κ0, map_one, Units.val_one]⟩
    · obtain ⟨s, hs⟩ := hi x hx
      obtain ⟨s', -, e⟩ := mem_of_unit ⊤ ((unitsK R).inv_mem (hu x)) ⟨s, trivial, hs⟩
      rw [eκ x, inv_mul_cancel_left] at e
      exact ⟨s', e⟩
  have κb : ∀ y z, ∃ v : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
      algebraMap R _ (v : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R) := fun y z => by
    obtain ⟨v, hv, e⟩ := hb y z
    obtain ⟨v', ev'⟩ := mul_mem (mul_mem hv (mul_mem (mul_mem (hu (y + h' z)) (hu (h y))) (hu z)))
      (inv_mem (mul_mem (mul_mem (hu (h y + z)) (hu y)) (hu (h' z))))
    refine ⟨v', congrArg Units.val (?_ : _ = Units.map (algebraMap R (FractionRing R)).toMonoidHom v' * _)⟩
    rw [ev']
    simp only [eκ] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  obtain ⟨ρ, eρ⟩ := hP κ κn κ0 κc κi κb y
  obtain ⟨v, ev'⟩ := mul_mem (pow_mem (hu y) N) (inv_mem (mul_mem (hu y) (hu (h y))))
  refine ⟨?_, v * ρ, ?_⟩
  · obtain ⟨s, hs⟩ := κi y
    obtain ⟨s', -, e⟩ := mem_of_unit ⊤ (hu y) ⟨s, trivial, hs⟩
    exact ⟨s', eκ y ▸ e⟩
  · have e1 : algebraMap R (FractionRing R) v = ((u y ^ N * (u y * u (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) :=
      congrArg Units.val ev'
    rw [map_mul, e1, eκ y, eκ (h y), mul_pow]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, eρ]
    have := (u y).ne_zero
    have := (u (h y)).ne_zero
    have := (κ (h y)).ne_zero
    field_simp

theorem gs_scal {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (r : R) :
    gs (𝟙 _) z ⊤ (scal (jK R) r) = ev z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((TK R).left.presheaf.germ ⊤ z trivial).hom nat.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∃ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) ∧ (∀ y, y ≠ 0 → r y ∈ maximalIdeal R) ∧ (∀ e : ℕ, {y | r y ∉ maximalIdeal R ^ e}.Finite) ∧ ∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val := by
  intro R _ _ _ _ D a a' h h' hE N _ hP
  obtain ⟨ga, k, hk⟩ := exists_psiScal R D.toPre
  have key := scalars_int k h h' N
    (fun x => by
      obtain ⟨u, e⟩ := even_part D.toPre ga k hk D.psi_even x
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x y w => by
      obtain ⟨u, e⟩ := cub_part D.toPre ga k hk D.tau_bimult x y w
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x hx => by
      obtain ⟨s, -, e⟩ := (PsiScalIn.main_local D.toPre ga k hk x _).1 (D.psi_pos x hx)
      exact ⟨s, e.symm⟩)
    (bal_part D.toPre ga k hk hE) hP.2
  choose s hs using fun y => (key y).1
  choose ρ hρ using fun y => (key y).2
  have hm : ∀ y (I : Ideal R), D.toPre.PsiIn y I → ρ y * s y ∈ I := fun y I hy => by
    obtain ⟨t, ht, e⟩ := (PsiScalIn.main_local D.toPre ga k hk y _).1 hy
    obtain rfl : t = s y := IsFractionRing.injective R (FractionRing R) (e.trans (hs y))
    exact I.mul_mem_left _ ht
  refine ⟨fun y => ρ y * s y, ga, fun y => (hk y).1, fun y hy => hm y _ (D.psi_pos y hy),
    fun e => (D.psi_tendsto e).subset fun y hy hi => hy (hm y _ hi), fun y z J hJ => ?_⟩
  have hψ : ∀ χ, val (D.toPre.psi χ) (𝟙 _) z J =
      Units.map (ev z).toMonoidHom (k χ) * val (ga χ) (toUnit (TK R)).left z J := fun χ =>
    Units.ext (((hk χ).2 (TK R) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have e : algebraMap R (FractionRing R) (ρ y * s y) = (k y ^ N * (k (h y))⁻¹).val := by
    rw [hρ, map_mul, hs]
  rw [gs_scal, e, hψ, hψ]
  refine congrArg Units.val (?_ : _ = Units.map (ev z).toMonoidHom (k y ^ N * (k (h y))⁻¹) * _)
  rw [map_mul, map_pow, map_inv, mul_pow, mul_inv, _root_.mul_mul_mul_comm]

end GlobalTheory.MumInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAdjointNefSeparateEtaleFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleSep


set_option maxHeartbeats 1000000 in
theorem sections_separate_fibre : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)], IsProjOver p → IsProjOver (f ≫ p) → 1 ≤ n → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (K : CanonLB (f ≫ p) n) (N : LB W) (hN : N.IsLB) (N' B : LB M) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : Sp ℂ ⟶ W) (U : W.Opens), IsNef ℂ N → IsBig ℂ N → IsNef ℂ (N.pull f) → IsBig ℂ (N.pull f) → IsNef ℂ N' → (n + 1).choose 2 < m → cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN' → x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → Etale (f ∣_ U) → (∀ (Z : Closeds W) (e : ℕ), IsIrreducible (Z : Set W) → Set.range x ⊆ Z → 1 ≤ e → topologicalKrullDim (Z : Set W) = e → 0 < interNumRed ℂ Z fun _ : Fin e => N) → ∀ (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M)), Function.Injective z → (∀ j, z j ≫ f = x) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 (f ≫ p) (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) → a = 0 := by
  intro hK hNN M W _ _ p f _ n _ _ hp hpM hn1
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  intro K N hN N' B hN' hB m x U hNn hNb hNfn hNfb hN'n hm hBc hxp hxU hEt hpos J _ z hzi hz k hk a hrel
  haveI : IsLocallyNoetherian W := by
    haveI := SmoothOfRelativeDimension.smooth n p; exact LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsLocallyNoetherian M := by
    haveI := SmoothOfRelativeDimension.smooth n (f ≫ p); exact LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  set c₀ := (n + 1).choose 2 with hc₀def
  set pt : Sp ℂ := IsLocalRing.closedPoint ℂ with hpt
  set x₀ : W := x pt with hx₀
  have hrange : ∀ Z : Closeds W, x₀ ∈ Z → Set.range x ⊆ Z := by
    rintro Z h _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q pt]
  have hx₀c : IsClosed ({x₀} : Set W) := GlobalTheory.T.isClosed_image_section_projective_over_field ℂ W p x hp hxp
  have hx₀U : x₀ ∈ U := hxU (Set.mem_univ pt)

  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ := GlobalTheory.nef_big_of_cls_eq_smul_add_smul hNN ℂ W p hp N N hN hN (2 * c₀ + 1) 0
    hNn hNb hNn (by omega)
  obtain ⟨m', D₀, U', hm', hD₀, hcur, hxU', hklt, hnk⟩ := GlobalTheory.KollarApp.isolatedNonKlt_smooth hK.2 W p n hp hn1
    N₀ 2 x₀ two_pos hn₀ hb₀ hx₀c (fun Z e hZ hxZ he hdim => by
      have h1 := hpos Z e hZ (hrange Z hxZ) he hdim
      have h2 := GlobalTheory.mixExp_interNumRed hNN ℂ W p hp N N N₀ hN hN h₀ (2 * c₀ + 1) 0 Z e hNn hNn hc₀ hdim
      have h3 : ((2 * c₀ + 1 : ℕ) : ℤ) ^ e ≤ interNumRed ℂ Z (fun _ : Fin e => N₀) := by
        have : (0 : ℤ) ≤ ((2 * c₀ + 1 : ℕ) : ℤ) ^ e := by positivity
        nlinarith
      have h3' : (((2 * c₀ + 1 : ℕ) : ℝ)) ^ e ≤ (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) := by
        exact_mod_cast h3
      have h4 : (((c₀ : ℕ) : ℝ) * 2) ^ e < ((2 * c₀ + 1 : ℕ) : ℝ) ^ e := by
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        exact_mod_cast (by omega : c₀ * 2 < 2 * c₀ + 1)
      rw [lt_div_iff₀ (by positivity), ← mul_pow]
      push_cast at h4 h3' ⊢
      linarith)

  obtain ⟨D₁, hD₁, heq⟩ := _root_.GlobalTheory.Cartier.exists_pull_dominant M W f D₀ hD₀
  have hcls := _root_.GlobalTheory.PullCartier.cls_toLB_pull M W f D₀ D₁ heq

  obtain ⟨M₀, hM₀, hcM, hnM, hbM⟩ := GlobalTheory.nef_big_of_cls_eq_smul_add_smul hNN ℂ M (f ≫ p) hpM (N.pull f) N'
    (pull_isLB hN f) hN' (2 * m - 2 * c₀ - 1) 2 hNfn hNfb hN'n (by omega)
  have hclsN : cls (N.pull f) (pull_isLB hN f) = CechPic.pull f (cls N hN) := cls_pull hN f _
  obtain ⟨Jd, hJ, hvan⟩ := GlobalTheory.NadelApp.nadel_canonical_add hK.1 M (f ≫ p) n hpM K B M₀ hB D₁ m' 2 hm' two_pos
    hD₁ hnM hbM (fun C hC => by
      have e1 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM B (N.pull f) N' hB (pull_isLB hN f) hN' m 1
        C hC (by rw [hBc, one_smul, hclsN])
      have e2 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM M₀ (N.pull f) N' hM₀ (pull_isLB hN f) hN'
        (2 * m - 2 * c₀ - 1) 2 C hC hcM
      have e3 := interNumRed_one_congr (k := ℂ) (isLB_toLB D₁) (pull_isLB (isLB_toLB D₀) f)
        (hcls.trans (cls_pull (isLB_toLB D₀) f _).symm) C
      have e4 := GlobalTheory.T.intersectionNumber_pullback_proportional_of_proportional M W p f hp hpM (toLB D₀) N₀ (isLB_toLB D₀) h₀ 2 m' (fun C' hC' => by
        have := hcur C' hC'
        have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
        rw [Nat.cast_ofNat, div_eq_div_iff hm'0 two_ne_zero] at this
        have h' : ((2 * interNumRed ℂ C' ![toLB D₀] : ℤ) : ℚ) = ((m' * interNumRed ℂ C' ![N₀] : ℤ) : ℚ) := by
          push_cast; linarith
        push_cast
        exact_mod_cast h') C hC
      have e5 := GlobalTheory.interNumRed_of_cls_eq_nsmul_add ℂ M (f ≫ p) hpM (N₀.pull f) (N.pull f) (N.pull f)
        (pull_isLB h₀ f) (pull_isLB hN f) (pull_isLB hN f) (2 * c₀ + 1) 0 C hC
        (by rw [cls_pull h₀ f _, hc₀, hclsN, zero_smul, add_zero, zero_smul, add_zero, map_nsmul])
      rw [e1, e3, e2]
      have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
      have e4' : ((interNumRed ℂ C ![(toLB D₀).pull f] : ℤ) : ℚ) = m' * (2 * c₀ + 1) / 2 * interNumRed ℂ C ![N.pull f] := by
        have : (2 : ℚ) * interNumRed ℂ C ![(toLB D₀).pull f] = m' * interNumRed ℂ C ![N₀.pull f] := by exact_mod_cast e4
        rw [e5] at this
        push_cast at this
        linarith
      have hsub : ((2 * m - 2 * c₀ - 1 : ℕ) : ℚ) = 2 * m - 2 * c₀ - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [e4']
      push_cast [hsub]
      field_simp
      ring)

  set UM : M.Opens := f ⁻¹ᵁ (U ⊓ U') with hUM
  have hEtM : Etale (UM.ι ≫ f) := by
    haveI := hEt
    have hle : UM ≤ f ⁻¹ᵁ U := fun y hy => hy.1
    have e : UM.ι ≫ f = M.homOfLE hle ≫ (f ∣_ U) ≫ U.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    rw [e]; infer_instance
  have hkl := _root_.GlobalTheory.EtaleKlt.kltAt_iff_etale M W p f n m' UM D₀ D₁ hEtM hm' heq
  have hsupp : ∀ y ∈ UM, (y ∈ Jd.support ↔ f y = x₀) := by
    intro y hy
    rw [hJ, hkl y hy]
    have hyU' : f y ∈ U' := hy.2
    constructor
    · intro h; by_contra hne; exact h (hklt _ hyU' hne)
    · intro e; rw [e]; exact hnk
  have hfz : ∀ j, f (z j pt) = x₀ := fun j => by
    have := congrArg (fun h : Sp ℂ ⟶ W => h pt) (hz j)
    simpa using this
  have hzM : ∀ j, z j pt ∈ UM := fun j => by
    show f (z j pt) ∈ U ⊓ U'
    rw [hfz j]; exact ⟨hx₀U, hxU'⟩
  have hzp : ∀ j, z j ≫ f ≫ p = 𝟙 _ := fun j => by rw [← Category.assoc, hz j, hxp]
  have hzne : ∀ i j, i ≠ j → z i pt ≠ z j pt := fun i j hij e =>
    hij (hzi (_root_.GlobalTheory.section_eq_of_point_eq ℂ M (f ≫ p) (z i) (z j) (hzp i) (hzp j) e))
  funext j
  show a j = 0
  obtain ⟨V, hzV, hV⟩ := _root_.GlobalTheory.isolated_in_fibre_of_etale_restrict M W f U hEt (z j pt) (by rw [hfz j]; exact hx₀U)
  obtain ⟨s, hs, hs'⟩ := _root_.GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated_zero_else ℂ M (f ≫ p) hpM (tens K.bundle B) (isLB_tens K.isLB hB) Jd (z j pt) (V ⊓ UM)
    (GlobalTheory.T.isClosed_image_section_projective_over_field ℂ M (f ≫ p) (z j) hpM (hzp j)) ⟨hzV, hzM j⟩ (fun y hy => by
      rw [hsupp y hy.2, ← hfz j]
      exact ⟨hV y hy.1, fun e => e ▸ rfl⟩) (hvan 1 one_pos)
  have h1 := hrel (H0.ofSec (f ≫ p) ⊤ s)
  rw [Finset.sum_eq_single j (fun i _ hij => by
      have : H0.val (z i) (k i) le_top (hk i) (H0.ofSec (f ≫ p) ⊤ s) = 0 := by
        by_contra hne
        exact hs' _ ((hsupp _ (hzM i)).2 (hfz i)) (hzne i j hij)
          ((GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus ℂ M (f ≫ p) _ s (z i) (k i) (hk i)).1 hne)
      rw [this, mul_zero]) (fun h => absurd (Finset.mem_univ j) h)] at h1
  exact (mul_eq_zero.1 h1).resolve_right ((GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus ℂ M (f ≫ p) _ s (z j) (k j) (hk j)).2 hs)

end GlobalTheory.EtaleSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantKthRootLabelledPointUpToRootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.thetaConst_pow_eq_at_root | exact GlobalTheory.thetaConst_pow_eq_at_root | (intros; apply GlobalTheory.thetaConst_pow_eq_at_root <;> assumption)
end

