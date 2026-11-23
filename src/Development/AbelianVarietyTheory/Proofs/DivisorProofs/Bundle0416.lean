module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderFaithfulLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0381

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCompPosOfAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.UPel.HT

theorem trace_comp_pos_of_adjoint {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u)
    (T T' : V →ₗ[ℝ] V) (hadj : ∀ u v, g (T u) v = g u (T' v)) (hT' : T' ≠ 0) :
    0 < LinearMap.trace ℝ V (T ∘ₗ T') := by
  letI core : InnerProductSpace.Core ℝ V :=
    { inner := fun x y => g x y
      conj_inner_symm := fun x y => by simpa using hs y x
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · simpa using (hp x h).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hp x h).ne' hx }
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b]
  have key : ∀ i, ⟪b i, (T ∘ₗ T') (b i)⟫_ℝ = g (T' (b i)) (T' (b i)) := by
    intro i
    show g (b i) (T (T' (b i))) = _
    rw [hs, hadj]
  simp only [key]
  have hnn : ∀ i, 0 ≤ g (T' (b i)) (T' (b i)) := fun i => by
    by_cases h : T' (b i) = 0
    · simp [h]
    · exact (hp _ h).le
  obtain ⟨i, hi⟩ : ∃ i, T' (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hT'
    exact b.toBasis.ext (fun i => by simpa using h i)
  exact Finset.sum_pos' (fun i _ => hnn i) ⟨i, Finset.mem_univ _, hp _ hi⟩

theorem trace_mul_star_pos : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), x ≠ 0 →
    0 < LinearMap.trace ℤ D.La (DistribSMul.toLinearMap ℤ D.La (x * (D.star x).unop)) := by
  intro p _ D x hx
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨J, hJJ, hJinv, hpos, hcomm, -⟩ := D.dom
  let A : D.O → (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) := fun b =>
    (DistribSMul.toLinearMap ℤ D.La b).baseChange ℝ
  have hcomp : A x ∘ₗ A (D.star x).unop =
      (DistribSMul.toLinearMap ℤ D.La (x * (D.star x).unop)).baseChange ℝ := by
    clear hcomm hpos hJinv hJJ
    simp only [A]
    rw [← LinearMap.baseChange_comp]
    congr 1
    ext y
    show x • ((D.star x).unop • y) = (x * (D.star x).unop) • y
    rw [mul_smul]
  have hA : ∀ b (r : ℝ) (y : D.La), A b (r ⊗ₜ y) = r ⊗ₜ (b • y) := fun _ _ _ => rfl
  have hAJ : ∀ b, J ∘ₗ A b = A b ∘ₗ J := fun b => hcomm b (A b) (fun y => rfl)
  have hEF : ∀ y z : D.La, D.EF y z = - D.EF z y := by
    intro y z
    have h := D.alt (y + z)
    simp only [map_add (f := _), LinearMap.add_apply, D.alt y, D.alt z, zero_add, add_zero] at h
    omega
  have hanti : ∀ u v, D.EF.baseChange ℝ u v = - D.EF.baseChange ℝ v u := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hEF y z]
        simp only [zsmul_eq_mul, Int.cast_neg]
        ring
      | add v w hv hw =>
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [hv, hw]
        ring
    | add u w hu hw =>
      simp only [map_add (f := _), LinearMap.add_apply]
      rw [hu, hw]
      ring
  have hadjB : ∀ b u v, D.EF.baseChange ℝ (A b u) v = D.EF.baseChange ℝ u (A (D.star b).unop v) := by
    intro b u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [hA, hA, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, D.adj]
      | add v w hv hw => simp only [map_add (f := _), LinearMap.add_apply, hv, hw]
    | add u w hu hw => simp only [map_add (f := _), LinearMap.add_apply, hu, hw]
  have hsym : ∀ u v, D.EF.baseChange ℝ (J u) v = D.EF.baseChange ℝ (J v) u := by
    intro u v
    rw [← hJinv (J v) u, hJJ, map_neg, LinearMap.neg_apply, hanti v (J u), neg_neg]
  have hadjg : ∀ u v, (D.EF.baseChange ℝ ∘ₗ J) (A x u) v =
      (D.EF.baseChange ℝ ∘ₗ J) u (A (D.star x).unop v) := by
    intro u v
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.comp_apply J (A x), hAJ, LinearMap.comp_apply, hadjB]
  have hinj : ∀ y : D.La, (1 : ℝ) ⊗ₜ[ℤ] y = 0 → y = 0 := by
    intro y hy
    refine (Module.forall_dual_apply_eq_zero_iff ℤ y).1 fun φ => ?_
    have h := congrArg (fun t => TensorProduct.rid ℤ ℝ (LinearMap.baseChange ℝ φ t)) hy
    simp only [LinearMap.baseChange_tmul, TensorProduct.rid_tmul, map_zero] at h
    simpa using h
  have hT' : A (D.star x).unop ≠ 0 := by
    intro h0
    apply hx
    have hz : ∀ y : D.La, (D.star x).unop • y = 0 := fun y => hinj _ (by
      have := LinearMap.congr_fun h0 ((1 : ℝ) ⊗ₜ y)
      rwa [hA, LinearMap.zero_apply] at this)
    have h1 := _root_.GlobalTheory.HTFaith.faithful p D _ hz
    rw [← D.star_star x, h1]
    simp
  have htr := trace_comp_pos_of_adjoint (D.EF.baseChange ℝ ∘ₗ J)
    (fun u v => by simp only [LinearMap.comp_apply]; exact hsym u v)
    (fun u hu => by simpa only [LinearMap.comp_apply] using hpos u hu)
    (A x) (A (D.star x).unop) hadjg hT'
  rw [hcomp, LinearMap.trace_baseChange] at htr
  simpa using htr

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFormExistsPowSmulEqZeroOfIsLocalization
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechDR

theorem mOm_two_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (x : Om R A 2) :
    (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x =
      GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) x := by
  set h := SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)
  let L : Om R A 2 →ₗ[A] Om R B 2 :=
    { toFun := h.mOm 2
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply]; exact algebraMap_smul B a _ }
  have e : L = GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti, hv, ← wedge_eq_ιMulti]
    change h.mOm 2 _ = _
    rw [h.mOm_wedge, h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), wedge_eq_ιMulti]
    congr 1
    ext i; fin_cases i <;> rfl
  exact LinearMap.congr_fun e x

theorem twoForm_exists_pow_smul_eq_zero_of_isLocalization {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (c : A)
    [IsLocalization.Away c B] (x : Om R A 2)
    (hx : (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x = 0) :
    ∃ n : ℕ, c ^ n • x = 0 := by
  haveI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A B) 2
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c) B _).2 hb
  rw [mOm_two_eq_exteriorPowerMapOver, ← map_zero (GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B))] at hx
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := c) hx
  exact ⟨n, hn.trans (smul_zero _)⟩

theorem twoForm_exists_pow_smul_eq_zero_of_algHom {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (c : A)
    (hc : @IsLocalization.Away A _ c B _ f.toRingHom.toAlgebra) (x : Om R A 2)
    (hx : (SemiHom.of_algHom f).mOm 2 x = 0) : ∃ n : ℕ, c ^ n • x = 0 := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact twoForm_exists_pow_smul_eq_zero_of_isLocalization c x hx

theorem twoForm_sep_of_basis : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (η : Om R' ((OAff s').obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm (OAff s') 2 u η = 0) → η = 0) := by
  intro R' _ X' s' C' _ G hcov T η hη
  obtain ⟨n, b, hb, hf⟩ := hcov T
  have key : ∀ i, ∃ m : ℕ, b i ^ m • η = 0 := by
    intro i
    let U : X'.affineOpens := T.unop
    let c : Γ(X', U.1) := b i
    let V : X'.affineOpens := ⟨X'.basicOpen c, U.2.basicOpen c⟩
    have hle : V ≤ U := X'.basicOpen_le c
    let u : T ⟶ Opposite.op V := (homOfLE hle).op
    have hu : IsUnit (mp (OAff s') u (b i)) := X'.toRingedSpace.isUnit_res_basicOpen c
    obtain ⟨t, v, w, hvw⟩ := hf i (Opposite.op V) u hu
    have h0 : pOm (OAff s') 2 u η = 0 := by rw [← hvw, pOm_comp, hη t v, map_zero]
    exact twoForm_exists_pow_smul_eq_zero_of_algHom (mp (OAff s') u) (b i)
      (U.2.isLocalization_basicOpen c) η h0
  choose m hm using key
  have hN : ∀ i, b i ^ (∑ j, m j) • η = 0 := fun i ↦ by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (m j))
      (Finset.mem_univ i))
    rw [hk, pow_add, mul_comm, mul_smul, hm i, smul_zero]
  have := Ideal.span_pow_eq_top _ hb (∑ j, m j)
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at this
  obtain ⟨r, hr⟩ := this
  rw [← one_smul ((OAff s').obj T) η, ← hr, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [Function.comp_apply, mul_smul, hN i, smul_zero]

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreSections
section
open MvPolynomial

namespace GlobalTheory.UniformSerre

variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}

noncomputable def comp (e : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) : MvPolynomial σ R :=
  ∑ m ∈ Q.support, monomial m ((AddMonoidAlgebra.coeff Q m).val.coeff e)

theorem coeff_comp (e : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (comp e Q) m = (AddMonoidAlgebra.coeff Q m).val.coeff e := by
  classical
  rw [comp, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push_neg at h; rw [h]; simp


open scoped Classical in
noncomputable def liftFun (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, (mem_reesAlgebra_iff I _).2 (fun i => by
    rw [Polynomial.coeff_monomial_apply]; split_ifs with hi
    · subst hi; exact h
    · exact zero_mem _)⟩ else 0

theorem liftFun_zero (e : ℕ) : liftFun I e 0 = 0 := by
  unfold liftFun; rw [dite_eq_left (zero_mem _)]; ext1; simp

noncomputable def lift (I : Ideal R) (e : ℕ) (P : MvPolynomial σ R) : MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ P.support, monomial m (liftFun I e (AddMonoidAlgebra.coeff P m))

theorem coeff_lift (e : ℕ) (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (lift I e P) m = liftFun I e (AddMonoidAlgebra.coeff P m) := by
  classical
  rw [lift, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push_neg at h; rw [h, liftFun_zero]

theorem comp_lift (e e' : ℕ) (P : MvPolynomial σ R) (hP : ∀ m, AddMonoidAlgebra.coeff P m ∈ I ^ e) :
    comp e' (lift I e P) = if e' = e then P else 0 := by
  ext m
  rw [coeff_comp, coeff_lift]
  unfold liftFun; rw [dite_eq_left (hP m)]
  show (Polynomial.monomial e (AddMonoidAlgebra.coeff P m)).coeff e' = _
  rw [Polynomial.coeff_monomial]
  by_cases h : e' = e
  · subst h; simp
  · simp [Finsupp.single_apply, h, Ne.symm h]

theorem comp_sub (e : ℕ) (Q₁ Q₂ : MvPolynomial σ (reesAlgebra I)) :
    comp e (Q₁ - Q₂) = comp e Q₁ - comp e Q₂ := by
  ext m; rw [coeff_sub, coeff_comp, coeff_comp, coeff_comp, coeff_sub]
  exact Polynomial.coeff_sub _ _ _

theorem comp_X_pow_mul (e : ℕ) (k : σ) (L : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) :
    comp e (X k ^ L * Q) = X k ^ L * comp e Q := by
  ext m
  rw [coeff_comp, X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul', coeff_monomial_mul']
  split_ifs <;> simp [coeff_comp]

theorem isHomogeneous_lift {e t : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous t) :
    (lift I e P).IsHomogeneous t :=
  fun d hd => hP (fun h0 => hd (by rw [coeff_lift, h0, liftFun_zero]))

theorem isHomogeneous_comp {e t : ℕ} {Q : MvPolynomial σ (reesAlgebra I)} (hQ : Q.IsHomogeneous t) :
    (comp e Q).IsHomogeneous t :=
  fun d hd => hQ (fun h0 => hd (by rw [coeff_comp, h0]; simp))

theorem isHomogeneous_sub' {S : Type} [CommRing S] {P Q : MvPolynomial σ S} {t : ℕ}
    (hP : P.IsHomogeneous t) (hQ : Q.IsHomogeneous t) : (P - Q).IsHomogeneous t := by
  rw [← mem_homogeneousSubmodule] at *; exact Submodule.sub_mem _ hP hQ

end GlobalTheory.UniformSerre


open GlobalTheory.UniformSerre in
theorem GlobalTheory.uniform_serre_sections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (F i).IsHomogeneous (d + N)) → (∀ i m, AddMonoidAlgebra.coeff (F i) m ∈ I ^ e) → (∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * (X j ^ N * F i - X i ^ N * F j) ∈ J e) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous d ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ e) ∧ ∀ i, ∃ L : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ L * (F i - X i ^ N * G) ∈ J e := by
  open GlobalTheory.UniformSerre in
  intro R _ _ I n J hJ
  obtain ⟨𝔞, hgr, hmem⟩ := _root_.GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal R I n J hJ
  obtain ⟨d₀, hd₀⟩ := _root_.GlobalTheory.exists_form_of_compatible_fractions (reesAlgebra I) n 𝔞 hgr
  refine ⟨d₀, fun d hd e N F hFh hFc hFcomp => ?_⟩
  have hmemiff : ∀ t (H : MvPolynomial (Fin (n+1)) (reesAlgebra I)), H.IsHomogeneous t →
      (H ∈ 𝔞 ↔ ∀ e', comp e' H ∈ J e') := by
    intro t H hH
    rw [hmem t H hH]
    constructor
    · intro h e'; exact h e' _ (fun m => coeff_comp e' H m)
    · intro h e' G hG
      have : G = comp e' H := by ext m; rw [hG m, coeff_comp]
      rw [this]; exact h e'
  obtain ⟨G', hG'h, hG'⟩ := hd₀ d hd N (fun i => lift I e (F i)) (fun i => isHomogeneous_lift (hFh i)) (by
    intro i j
    obtain ⟨L, hL⟩ := hFcomp i j
    refine ⟨L, ?_⟩
    have hhom := ((((isHomogeneous_X (reesAlgebra I) i).mul (isHomogeneous_X _ j)).pow L).mul
      (isHomogeneous_sub' (((isHomogeneous_X _ j).pow N).mul (isHomogeneous_lift (I := I) (e := e) (hFh i)))
        (((isHomogeneous_X _ i).pow N).mul (isHomogeneous_lift (I := I) (e := e) (hFh j)))))
    rw [hmemiff _ _ hhom]
    intro e'
    rw [mul_pow, mul_assoc, comp_X_pow_mul, comp_X_pow_mul, comp_sub, comp_X_pow_mul, comp_X_pow_mul,
      comp_lift _ _ _ (hFc i), comp_lift _ _ _ (hFc j)]
    split_ifs with h
    · subst h; rw [← mul_assoc, ← mul_pow]; exact hL
    · simp)
  refine ⟨comp e G', isHomogeneous_comp hG'h, fun m => ?_, fun i => ?_⟩
  · rw [coeff_comp]; exact (mem_reesAlgebra_iff I _).1 (AddMonoidAlgebra.coeff G' m).2 e
  · obtain ⟨L, hL⟩ := hG' i
    refine ⟨L, ?_⟩
    have hhom := ((isHomogeneous_X (reesAlgebra I) i).pow L).mul
      (isHomogeneous_sub' (isHomogeneous_lift (I := I) (e := e) (hFh i))
        (by rw [show d + N = 1 * N + d by ring]; exact ((isHomogeneous_X _ i).pow N).mul hG'h))
    have := (hmemiff _ _ hhom).1 hL e
    rwa [comp_X_pow_mul, comp_sub, comp_X_pow_mul, comp_lift _ _ _ (hFc i), if_pos rfl] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaLocalAnyResidueCharOfLieAlgebra
section
noncomputable section

namespace GlobalTheory.UnitLemma.UnrAny

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

section Assembly

variable {K K' : UQ}

def prodEquiv (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    ((overExt φ B₁ ((RingHom.fst B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.fst (hψ e))
        (fun e => congrArg Prod.fst (hσ e))).prod
      (overExt φ B₂ ((RingHom.snd B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.snd (hψ e))
        (fun e => congrArg Prod.snd (hσ e)))).A ≃ₐ[K'.E] (overExt φ (B₁.prod B₂) ψ hψ hσ).A :=
  { RingEquiv.refl (B₁.A × B₂.A) with commutes' := fun _ => rfl }

theorem prodEquiv_isIso (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    Orbit.IsIso (prodEquiv φ B₁ B₂ ψ hψ hσ) :=
  ⟨fun _ => rfl, rfl⟩

theorem prod_unitary (B₁ B₂ : InvAlg K) (hu₁ : B₁.g * B₁.σ B₁.g = 1) (hu₂ : B₂.g * B₂.σ B₂.g = 1) :
    (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 :=
  Prod.ext hu₁ hu₂

theorem prod_integral (B₁ B₂ : InvAlg K) (hi₁ : IsIntegral K.O B₁.g) (hi₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g := by
  obtain ⟨p₁, hp₁, e₁⟩ := hi₁
  obtain ⟨p₂, hp₂, e₂⟩ := hi₂
  refine ⟨p₁ * p₂, hp₁.mul hp₂, ?_⟩
  rw [← aeval_def] at e₁ e₂ ⊢
  have h1 : (aeval (B₁.prod B₂).g (p₁ * p₂)).1 = aeval B₁.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  have h2 : (aeval (B₁.prod B₂).g (p₁ * p₂)).2 = aeval B₂.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  refine Prod.ext ?_ ?_
  · rw [h1, map_mul, e₁, zero_mul]; rfl
  · rw [h2, map_mul, e₂, mul_zero]; rfl

end Assembly

theorem unitLemma_local_of_lie_any : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  have hsepP : (B₁.prod B₂).P.Separable := by rw [Orbit.prod_P]; exact hsep
  have huP := prod_unitary B₁ B₂ hu₁ hu₂
  have hiP := prod_integral B₁ B₂ hi₁ hi₂
  obtain ⟨d, hd, hcard⟩ := _root_.GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any K B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  obtain ⟨K', φ, hq, hc, hv, hodd, hfin, hz⟩ := _root_.GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext K d hd
  have hU : IsUnrExt K K' d φ := ⟨hq, hc, hv, hodd, hfin⟩
  obtain ⟨ψ, hψ, hσ, hO, s, hs, hres⟩ := _root_.GlobalTheory.UnitLemma.UnrAny.exists_unr_embedding_any K (B₁.prod B₂) huP hsepP hiP hl d hcard K' φ hU hz
  obtain ⟨Q, hQ1, hQ2⟩ := _root_.GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO hl hsepP hiP s hres
  have hiso := prodEquiv_isIso φ B₁ B₂ ψ hψ hσ
  set ψ₁ := (RingHom.fst B₁.A B₂.A).comp ψ with hψ₁
  set ψ₂ := (RingHom.snd B₁.A B₂.A).comp ψ with hψ₂
  have h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e := fun e => congrArg Prod.fst (hψ e)
  have h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e) := fun e => congrArg Prod.fst (hσ e)
  have h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e := fun e => congrArg Prod.snd (hψ e)
  have h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e) := fun e => congrArg Prod.snd (hσ e)
  set C₁ := overExt φ B₁ ψ₁ h₁ h₁' with hC₁
  set C₂ := overExt φ B₂ ψ₂ h₂ h₂' with hC₂
  have hPP : C₁.P * C₂.P = (overExt φ (B₁.prod B₂) ψ hψ hσ).P := by
    rw [← Orbit.prod_P, ← hiso.charpoly_eq_of_isIso]
  have hO₁ : ∀ y : K'.O, ψ₁ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO₂ : ∀ y : K'.O, ψ₂ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO' : ∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈
      Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A) := fun y => hO y
  have hQ : ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = C₁.P * C₂.P ∧
      Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O (s : K'.O))) ^ Q.natDegree :=
    ⟨Q, hQ1.trans hPP.symm, hQ2⟩

  have hsep' : (C₁.P * C₂.P).Separable := by
    rw [hPP]
    exact _root_.GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable K K' d φ hU (B₁.prod B₂) ψ hψ hσ hsepP
  have hId := _root_.GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any hL K' C₁ C₂ hu₁ hu₂ hsep' s hs hQ

  have hst : ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)),
      (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
      (overExt φ B ψ hψ hσ).stSum = B.stSum := by
    intro B ψ hψ hσ hO'
    unfold InvAlg.stSum
    exact finsum_congr fun k => _root_.GlobalTheory.UnitLemma.Unr.N_overExt K K' d φ hU B ψ hψ hσ hO' _
  have hkap : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
    unfold InvAlg.kapSum
    refine finsum_congr fun k => ?_
    have hN : (C₁.prod C₂).N k.rep = (B₁.prod B₂).N k.rep := by
      rw [← hiso.N_eq]
      exact _root_.GlobalTheory.UnitLemma.Unr.N_overExt K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO _
    rw [hN]
    congr 1
    set x := (Quot.out k).1 with hx
    have hfix : B₁.σ ((x : (C₁.prod C₂).A).1) = (x : (C₁.prod C₂).A).1 := congrArg Prod.fst (Quot.out k).2
    let x₁ : B₁.Aˣ := Units.map (MonoidHom.fst B₁.A B₂.A) x
    have := _root_.GlobalTheory.UnitLemma.Unr.eta_overExt K K' d φ hU hd B₁ ψ₁ h₁ h₁' x₁ hfix
    exact this
  have hres' := _root_.GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr K K' d φ hU hd B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO' hsep s hQ
  unfold InvAlg.Identity at hId ⊢
  rw [hkap, hst B₁ ψ₁ h₁ h₁' hO₁, hst B₂ ψ₂ h₂ h₂' hO₂] at hId
  rw [← hId, hres', hq]
  congr 1
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [show -((2 * (m : ℤ) + 1) * val K'.O (resultant C₁.P C₂.P)) =
      (2 * (m : ℤ) + 1) * (-val K'.O (resultant C₁.P C₂.P)) by ring, zpow_mul]
  congr 1
  rw [show (2 * (m : ℤ) + 1) = ((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, Odd.neg_pow ⟨m, rfl⟩]

end GlobalTheory.UnitLemma.UnrAny
end
end

