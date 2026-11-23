module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_io : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ y' : N'.X, GtRelV W φ e wv (N'.io y') (fun j => N.io (e y' j)) := by
  intro F _ N N' r W φ e wv hT y'
  obtain ⟨-, -, he_add, -, hc, hw0, -, hψ⟩ := hT
  refine ⟨fun j => hc y' j, fun χ' => ?_⟩
  simp only [NumD.io_s, NumD.io_b]
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  let P : N'.X → Fˣ := fun a => ∏ i, ∏ j, N.τ (e a i) (e a j) ^ W i j
  have hψ' : ∀ a, N'.ψ a * U 1 = U (N'.c a) * P a := fun a => Units.ext (by
    simp only [Units.val_mul, U, Units.val_mk0, P]; exact hψ a)
  have key : ∀ i j, N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) /
      (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) *
        N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j))) =
      N.τ (e (y' + χ') i) (e (y' + χ') j) / N.τ (e y' i) (e y' j) / N.τ (e χ' i) (e χ' j) := by
    intro i j
    rw [he_add y' χ' i, he_add y' χ' j, add_comm (e y' i), add_comm (e y' j)]
    have h1 := N.τ_add_left (e χ' i) (e y' i) (e χ' j + e y' j)
    rw [N.c_add] at h1
    have h2 := N.τ_add_right (e χ' i) (e χ' j) (e y' j)
    have h3 := N.τ_add_right (e y' i) (e χ' j) (e y' j)
    have h4 := N.τ_symm (e y' j) (e χ' i)
    replace h1 := congrArg Additive.ofMul h1
    replace h2 := congrArg Additive.ofMul h2
    replace h3 := congrArg Additive.ofMul h3
    replace h4 := congrArg Additive.ofMul h4
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at h1 h2 h3 h4 ⊢
    linear_combination (norm := abel) h4 - h1 - h2 - h3
  have hQ : (∏ i, ∏ j, (N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) /
      (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) *
        N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j)))) ^ W i j : Fˣ) =
      P (y' + χ') / P y' / P χ' := by
    simp only [key, div_zpow, Finset.prod_div_distrib, P]
  rw [hQ, hU, hU, hU, hU]
  have hS := hψ' (y' + χ')
  rw [N'.c_add y' χ', mul_comm (N'.c y')] at hS
  have hy := hψ' y'
  have hx := hψ' χ'
  have E : N'.τ y' χ' * U (N'.c χ') * U (N'.c y') = P (y' + χ') / P y' / P χ' * U (N'.c χ' * N'.c y') * U 1 := by
    simp only [NumD.τ]
    replace hS := congrArg Additive.ofMul hS
    replace hy := congrArg Additive.ofMul hy
    replace hx := congrArg Additive.ofMul hx
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at hS hy hx ⊢
    linear_combination (norm := abel) hS - hy - hx
  have := congrArg Units.val E
  simpa only [Units.val_mul] using this

end GlobalTheory.Mum.TensTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniqueComponents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem eq_zero_of_sum_smul_matrix {G : Type} [AddCommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∑ j, M i j • f j = 0) (k : Fin r) : f k = 0 := by
  have e1 : f k = ∑ j, (1 : Matrix (Fin r) (Fin r) ℤ) k j • f j := by
    simp [Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_mul M hM]
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, h, smul_zero, Finset.sum_const_zero]

theorem eq_one_of_prod_zpow_matrix {G : Type} [CommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∏ j, f j ^ M i j = 1) (k : Fin r) : f k = 1 := by
  have := eq_zero_of_sum_smul_matrix M hM (fun j => Additive.ofMul (f j)) (fun i => by
    simpa [← ofMul_zpow, ← ofMul_prod] using congrArg Additive.ofMul (h i)) k
  simpa using this

theorem gtRelV_prod_tor_mul {F : Type} [Field F] {N : NumD F} {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (x : Fin r → N.X)
    (vs : Fin r → N.Gt) (T : Fin r → (Multiplicative N.X →* Fˣ)) :
    (∏ i, ∏ j, ((N.tor (T j) * vs j).s (x i) * (N.tor (T i) * vs i).s (x j) /
        (N.θ (N.c (x j)) (N.tor (T j) * vs j).b (N.c (x i)) * N.θ (N.c (x j)) (N.tor (T j) * vs j).b
            (N.tor (T i) * vs i).b *
          N.θ (N.c (x i)) (N.tor (T i) * vs i).b (N.c (x j) * (N.tor (T j) * vs j).b))) ^ W i j : Fˣ) =
      (∏ i, ∏ j, ((vs j).s (x i) * (vs i).s (x j) /
        (N.θ (N.c (x j)) (vs j).b (N.c (x i)) * N.θ (N.c (x j)) (vs j).b (vs i).b *
          N.θ (N.c (x i)) (vs i).b (N.c (x j) * (vs j).b))) ^ W i j) *
      ∏ i, ∏ j, (T j (Multiplicative.ofAdd (x i)) * T i (Multiplicative.ofAdd (x j))) ^ W i j := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← mul_zpow]
  congr 1
  simp only [NumD.tor_mul_s_apply, NumD.Gt.mul_b, NumD.tor_b, one_mul, div_eq_mul_inv]
  ac_rfl

theorem gtRelV_prod_single {G : Type} [CommGroup G] {A : Type} [AddCommGroup A] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Fin r → (Multiplicative A →* G)) (i : Fin r) (χ : A) :
    (∏ a, ∏ b, (T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) *
        T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b))) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ (W + W.transpose) i j := by
  simp only [mul_zpow, Finset.prod_mul_distrib]
  have h1 : (∏ a, ∏ b, T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W i j := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro a _ ha
      simp [Pi.single_apply, ha]
    · simp
  have h2 : (∏ a, ∏ b, T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W j i := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, Matrix.transpose_apply, zpow_add]

theorem gtRelV_components_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → IsUnit (W + W.transpose).det →
      ∀ (v' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv v' us → vs = us := by
  intro F _ N N' r W φ e wv hT hdet v' vs us hv hu
  have hb : ∀ j, (us j).b = (vs j).b := fun j => (hu.1 j).symm.trans (hv.1 j)
  have ht : ∀ j, ∃ t, N.tor t = us j / vs j := fun j =>
    (N.exists_tor_iff _).2 (by rw [div_eq_mul_inv, NumD.Gt.mul_b, NumD.Gt.inv_b, hb, mul_inv_cancel])
  choose T hT' using ht
  have hus : us = fun j => N.tor (T j) * vs j := funext fun j => by rw [hT', div_mul_cancel]
  subst hus
  have hwv : ∀ x, wv x ≠ 0 := hT.2.2.2.2.2.1
  have key : ∀ χ', (∏ i, ∏ j, (T j (Multiplicative.ofAdd (e χ' i)) * T i (Multiplicative.ofAdd (e χ' j))) ^ W i j) = 1 := by
    intro χ'
    have a := hv.2 χ'
    have b := hu.2 χ'
    rw [a, gtRelV_prod_tor_mul W (e χ') vs T] at b
    have c := mul_right_cancel₀ (hwv _) (mul_right_cancel₀ (hwv 1) b)
    have d := Units.ext c
    exact (mul_eq_left.1 d.symm)
  have hall : ∀ χ j, T j (Multiplicative.ofAdd χ) = 1 := by
    intro χ
    refine eq_one_of_prod_zpow_matrix (W + W.transpose) hdet (fun j => T j (Multiplicative.ofAdd χ)) fun i => ?_
    obtain ⟨χ', hχ'⟩ := hT.2.2.2.1.2 (Pi.single i χ)
    have := key χ'
    rw [hχ', gtRelV_prod_single W T i χ] at this
    exact this
  funext j
  have : T j = 1 := MonoidHom.ext fun m => by simpa using hall m.toAdd j
  rw [this, NumD.tor_one, _root_.one_mul]

end GlobalTheory.Mum.TensTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaImmersionPointsAgreeNearOfEqualRatios
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

variable {X H Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem sval_eq_secRatio_mul {φ : K → (H ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ H) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (ha : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (secRatio a b) * sval a r z J := by
  have hc := hJ.mem φ r
  have hm : r z ∈ nonzeroLocus a ⊓ (LB.LinComb L φ ε).U (fun k => J (r ≫ φ k)) := ⟨ha, hc⟩
  have e := congrArg (gs r z _) (secRatio_spec a b (fun k => J (r ≫ φ k)))
  rw [gs_mul r z _ hm, gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  exact e

theorem pullRatio_ι_comp {R : Type} [CommRing R] {M : ℕ} (P : H ⟶ PSpace R M) {U : H.Opens} {i : Fin (M + 1)}
    (hi : U ≤ P ⁻¹ᵁ chart R M i) (r : Z ⟶ H) (W : Z.Opens) (hW : W ≤ r ⁻¹ᵁ U)
    (h : ⊤ ≤ (W.ι ≫ r ≫ P) ⁻¹ᵁ chart R M i) (j : Fin (M + 1)) :
    pullRatio (W.ι ≫ r ≫ P) ⊤ i h j =
      (W.ι.appLE (r ⁻¹ᵁ U) ⊤ (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW))).hom
        ((r.app U).hom (pullRatio P U i hi j)) := by
  have hW' : ⊤ ≤ W.ι ⁻¹ᵁ (r ⁻¹ᵁ U) := W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW)
  rw [pullRatio_of_eq (Category.assoc W.ι r P).symm h ((hW'.trans ((W.ι ≫ r).preimage_mono hi))),
    ← appLE_pullRatio (W.ι ≫ r) hW', Scheme.Hom.app_eq_appLE, appLE_appLE]

end GlobalTheory.Mum.ThetaSep

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

theorem agree_near_of_minors : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k N : ℕ)
    (τ : Fin (N + 1) → SecK D.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤),
    IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) → ∀ (T : Over (Sp R)) (y y' : T ⟶ Y.H) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (∀ j l : Fin (N + 1), sval (τ j) y.left z J * sval (τ l) y'.left z J =
      sval (τ l) y.left z J * sval (τ j) y'.left z J) →
    ∃ W : T.left.Opens, z ∈ W ∧ W.ι ≫ y.left = W.ι ≫ y'.left := by
  intro R _ _ D Y k N τ hτ hImm T y y' z J hJ hrel
  have hmono : Mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := inferInstance
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y.left z)))
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y'.left z)))
  have ua : IsUnit (sval (τ j₀) y.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hj₀
  have ubi : IsUnit (sval (τ i) y'.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hi
  have ub : IsUnit (sval (τ j₀) y'.left z J) := by
    have h := hrel j₀ i
    have : IsUnit (sval (τ i) y.left z J * sval (τ j₀) y'.left z J) := h ▸ ua.mul ubi
    exact isUnit_of_mul_isUnit_right this
  have hj₀' : y'.left z ∈ nonzeroLocus (τ j₀) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).2 ub
  have hg : ∀ j, gs y.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) =
      gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) := by
    intro j
    have h := hrel j₀ j
    rw [sval_eq_secRatio_mul (τ j₀) (τ j) y.left z hJ hj₀,
      sval_eq_secRatio_mul (τ j₀) (τ j) y'.left z hJ hj₀'] at h
    refine ((ua.mul ub).mul_right_cancel ?_).symm
    calc _ = sval (τ j₀) y.left z J * (gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) *
          sval (τ j₀) y'.left z J) := by ring
      _ = _ := by rw [h]; ring
  have hW : ∀ j, ∃ W : T.left.Opens, z ∈ W ∧ ∃ (h₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀))
      (h₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀)),
      resG T.left h₁ ((y.left.app _).hom (secRatio (τ j₀) (τ j))) =
        resG T.left h₂ ((y'.left.app _).hom (secRatio (τ j₀) (τ j))) := by
    intro j
    have e := hg j
    rw [gs_eq _ z _ hj₀, gs_eq _ z _ hj₀'] at e
    obtain ⟨W, hzW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq T.left.presheaf z hj₀ hj₀' _ _ e
    exact ⟨W, hzW, leOfHom iU, leOfHom iV, e'⟩
  choose Wj hzWj h₁ h₂ heq using hW
  let W : T.left.Opens := Finset.univ.inf Wj
  have hzW : z ∈ W := Finset.inf_induction (p := fun U : T.left.Opens => z ∈ U) trivial
    (fun _ h _ h' => ⟨h, h'⟩) (fun j _ => hzWj j)
  have hWle : ∀ j, W ≤ Wj j := fun j => Finset.inf_le (Finset.mem_univ j)
  refine ⟨W, hzW, (cancel_mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ)).1 ?_⟩
  have hpre := toProj_preimage_chart Y.H.hom τ hτ j₀
  have hA : ∀ (r : T.left ⟶ Y.H.left), W ≤ r ⁻¹ᵁ nonzeroLocus (τ j₀) →
      ⊤ ≤ (W.ι ≫ r ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) ⁻¹ᵁ chart R N j₀ := fun r hr =>
    (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hr)).trans
      ((W.ι ≫ r).preimage_mono hpre.ge)
  have hy₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₁ j₀)
  have hy₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₂ j₀)
  simp only [Category.assoc]
  refine hom_ext ?_ fun _ => ⟨⊤, trivial, j₀, hA _ hy₁, hA _ hy₂, fun j => ?_⟩
  · simp only [Category.assoc, toProj_str]
    rw [Over.w y, Over.w y']
  · rw [pullRatio_ι_comp _ hpre.ge _ W hy₁, pullRatio_ι_comp _ hpre.ge _ W hy₂, pullRatio_toProj]
    have hW₁ : ⊤ ≤ W.ι ⁻¹ᵁ Wj j := W.ι_preimage_self.ge.trans (W.ι.preimage_mono (hWle j))
    rw [← appLE_resG W.ι (h₁ j) hW₁, ← appLE_resG W.ι (h₂ j) hW₁, heq j]

end GlobalTheory.Mum.ThetaSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariant
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.KCoinvGood

theorem augAt_le_SB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (v : Pl (F := F)) : augAt om v ≤ SB _ :=
  Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ

theorem acts_zero {F : Type} [Field F] [NumberField F] {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 := fun r _ => by
  have e : tens ev (0 : (κ → R) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [e, map_zero]

theorem ker_eq_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    (S A : Submodule ℂ V) (p : V →ₗ[ℂ] P) (hA : A ≤ LinearMap.ker p) (honto : S.map p = ⊤)
    (h : S ⊓ LinearMap.ker p = A ∨ S ⊓ LinearMap.ker p = S) : ∀ φ ∈ S, p φ = 0 ↔ φ ∈ A := by
  rcases h with h | h
  · intro φ hφ
    refine ⟨fun h0 => h ▸ ⟨hφ, h0⟩, fun hm => hA hm⟩
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    have hy' : y ∈ S ⊓ LinearMap.ker p := by rw [h]; exact hy
    exact hx hy'.2

theorem factor_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
    (S : Submodule ℂ V) (p : V →ₗ[ℂ] P) (l : V →ₗ[ℂ] ℂ) (honto : S.map p = ⊤) (hk : ∀ φ ∈ S, p φ = 0 → l φ = 0) :
    ∃ l₀ : P →ₗ[ℂ] ℂ, ∀ φ ∈ S, l φ = l₀ (p φ) := by
  set q := p.domRestrict S
  have hs : Function.Surjective q := by
    intro x
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : LinearMap.ker q ≤ LinearMap.ker (l.domRestrict S) := fun x hx => hk x.1 x.2 hx
  refine ⟨((LinearMap.ker q).liftQ (l.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap,
    fun φ hφ => ?_⟩
  have : (q.quotKerEquivOfSurjective hs).symm (p φ) = Submodule.Quotient.mk ⟨φ, hφ⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [this]

theorem kCoinv (hP : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.KCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm
  have ht := hm.triple
  have hf := hm.fin
  refine ⟨fun v hv => ?_, _root_.GlobalTheory.SoStable.so_stable hP F E σ B a a' G X om om' ht⟩
  haveI := hf.nontriv v
  have hnr := _root_.GlobalTheory.NuGood.not_root_of_unity F E σ B a a' G X om om' ht v hv
  have k1 : ∀ φ ∈ SB _, Rf.p v φ = 0 ↔ φ ∈ augAt om v :=
    ker_eq_of _ _ _ (hf.inv v) (hf.onto v) <|
      _root_.GlobalTheory.IrrCoinvV.irrV hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om v) (hf.inv v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh φ hφ.1 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero _ _)
            (by rw [map_zero]; exact hφ.2)
          rw [map_zero] at this; exact this⟩
  have k2 : ∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v :=
    ker_eq_of _ _ _ (hf.inv' v) (hf.onto' v) <|
      _root_.GlobalTheory.IrrCoinvSmall.irr_small hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om' v) (hf.inv' v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh 0 (zero_mem _) φ hφ.1 0 (zero_mem _) φ₁ hφ₁ (acts_zero _ _) hact
            (by rw [map_zero]; exact hφ.2.symm)
          rw [map_zero] at this; exact this.symm⟩
  refine ⟨k1, k2, fun t ξ => ?_, fun l hl => ?_⟩
  · have : ξ ∈ (SB _).map (Rf.p' v) := hf.onto' v ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := this
    obtain ⟨φ₀, h₀, hd⟩ := _root_.GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt hP F E σ B a a' G X om om' ht v hv hnr t φ hφ
    refine ⟨φ₀, h₀, ?_⟩
    have := hf.inv' v hd
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this.symm
  · exact factor_of _ _ _ (hf.onto' v) fun φ hφ h0 => hl ((k2 φ hφ).1 h0)

end GlobalTheory.KCoinvGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChange
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

namespace GlobalTheory.ModelChg

theorem det_ne_zero_of_hasSig {n r s : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : HasSig A r s) : A.det ≠ 0 := by
  obtain ⟨hrs, P, hP⟩ := h
  have hu : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin r) (Fin s) ℂ)
      (0 : Matrix (Fin s) (Fin r) ℂ) (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (Pᵀ * A * P.map star).rank ≤ A.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hP, h1] at h2
  simp at h2
  have h3 : A.rank = n := le_antisymm (by simpa using A.rank_le_card_width) (by omega)
  have h4 : LinearMap.range A.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h3)
  have h5 : Function.Surjective A.mulVec := LinearMap.range_eq_top.mp h4
  exact (Matrix.isUnit_iff_isUnit_det A |>.mp (Matrix.mulVec_surjective_iff_isUnit.mp h5)).ne_zero

theorem det_ne_zero_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (B : Base F E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ w, HasSig (c • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h1 := det_ne_zero_of_hasSig (h w)
  rw [Matrix.det_smul] at h1
  intro h0
  apply h1
  rw [show (J.map (B.emb w).1).det = (B.emb w).1 J.det from ((B.emb w).1.map_det J).symm, h0, map_zero, mul_zero]

theorem modelChange (hK : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.ModelChange := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ om₁ hP₁
  obtain ⟨a, ha, hco⟩ := _root_.GlobalTheory.goodModel_coords_rat_symplectic F E σ B.ψ n d X W M M₁ hP.good hP₁.good
  obtain ⟨e, c, hc, hev, hbij, hθ⟩ :=
    _root_.GlobalTheory.RatWeilOp.exists_intertwiner hK F E σ B n d X W M M₁ r s r' s' hP.base hP.herm hP.skew hP.good hP₁.good a ha hco
  obtain ⟨om₂, hW₂, hint⟩ := _root_.GlobalTheory.ModelTr.exists_isWeil_trans hK F E σ B n d X W M χX χW om r s r' s' hP M₁ hP₁.good e hev hbij
  have hX : X.J.det ≠ 0 :=
    det_ne_zero_of_sig B X.J 1 one_ne_zero (fun w => by simpa using hP.herm.sig w)
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_sig B W.J Complex.I Complex.I_ne_zero hP.skew.sig
  have huniq := GlobalTheory.T.adelicWeilRep_schrodingerModel_unique F E σ hP.base.cm n d X W M₁ B.ψ χX χW hP.base.std hP.herm.herm hX
    hP.skew.skew hWd om₂ om₁ hW₂ hP₁.weil
  refine ⟨e, c, hc, hev, hbij, fun Φ hΦ => ⟨hθ Φ hΦ, fun x => ?_⟩⟩
  rw [hint x Φ hΦ, huniq x (e Φ) (hbij.mapsTo hΦ)]

end GlobalTheory.ModelChg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialisationCoordinateNeZeroClassical
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.CoordNe

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem perp_top (S : ThetaSys o Ω) : S.perp ⊤ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : ∀ h : S.Gam, eStd S.g _ a h = 0 := fun h => ha h trivial
  funext k
  rcases k with i | i
  · have := ha' (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := ha' (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

theorem TT_eq_bot {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {z : M.Z} (hz : z ∈ U₀) :
    S.TT M z = ⊥ := by
  have h : S.supI M z = {x | S.th x ≠ 0} := by
    refine Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => ?_⟩⟩
    rw [div_eq_mul_inv]
    exact RatModel.ringOn_le_O hz (mul_mem (hO.le (S.th_mem i)) (hO.th_unit x hx))
  unfold ThetaSys.TT ThetaSys.HH
  rw [h, S.supp, perp_top]

theorem isOpen_TT (S : ThetaSys o Ω) (M : RatModel o Ω) : IsOpen {z | S.TT M z = ⊥} := by
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have : Finite S.Gam := inferInstance
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {w | M.Div S.th x w}, fun w hw => ?_,
    (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩
  have hsup : S.supI M z ⊆ S.supI M w := fun x hx => Set.mem_iInter₂.1 hw x hx
  have h : S.TT M w ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  exact le_bot_iff.1 (h.trans (le_of_eq hz))

theorem coord_ne_zero : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R) (D : DegData R (maximalIdeal R)), (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ α s, PsiCoord D.toPre α s → (ev s : PadicAlgCl p) ≠ 0 := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm hO x R _ _ _ j D hPsi p _ y ev hCen hfac α s hs h0
  let w : Sp (PadicAlgCl p) := (⊥ : PrimeSpectrum (PadicAlgCl p))
  have hW : IsOpen ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
    refine IsOpen.preimage (spMap j ≫ M.Z.fromSpecStalk x).continuous ?_
    rw [FinalForm.ab]
    exact isOpen_TT S M
  have hp : spMap ev (gPt p w) ∈ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G := by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hfac, FinalForm.ab]
    exact TT_eq_bot hO (hCen.2 ⟨w, rfl⟩)
  apply GlobalTheory.PsiCoordLocal.not_mem_of_coord hW hp (hPsi α) hs
  change (ev s : PadicAlgCl p) ∈ (⊥ : Ideal (PadicAlgCl p))
  exact h0

end GlobalTheory.Poinc.CoordNe
end

