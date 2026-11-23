module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaConstantOfThetaGroup
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

private theorem star_hermForm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian)
    (z w : Fin g → ℂ) : star (hermForm Hm z w) = hermForm Hm w z := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← herm.apply j i, star_star]
  ring

private theorem norm_exp_neg_hermForm_mul_exp_hermForm_eq_one {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian) (r : ℝ)
    (x a : Fin g → ℂ) :
    ‖Complex.exp (-((r : ℂ) * hermForm Hm x a)) * Complex.exp ((r : ℂ) * hermForm Hm a x)‖ = 1 := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add, ← star_hermForm_of_isHermitian Hm herm x a]
  simp

theorem thConst_liouville {g : ℕ} (lat : AddSubgroup (Fin g → ℂ))
    (span : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian)
    (k : ℤ) (x : Fin g → ℂ) (v : (Fin g → ℂ) → ℂ) (hv : Differentiable ℂ v)
    (hper : ∀ z, ∀ a ∈ lat, v (z + a) = v z * Complex.exp (-((k : ℂ) * Real.pi * hermForm Hm x a))) (z : Fin g → ℂ) :
    v z = v 0 * Complex.exp (-((k : ℂ) * Real.pi * hermForm Hm z x)) := by

  set c : ℝ := (k : ℝ) * Real.pi with hcdef
  have hcC : ((k : ℂ) * Real.pi) = (c : ℂ) := by rw [hcdef]; push_cast; ring
  simp only [hcC] at hper ⊢
  set f : (Fin g → ℂ) → ℂ := fun y => v y * Complex.exp ((c : ℂ) * hermForm Hm y x) with hf
  have hlin : ∀ y a : Fin g → ℂ, hermForm Hm (y + a) x = hermForm Hm y x + hermForm Hm a x := fun y a => by
    simp [hermForm, add_dotProduct]
  have hfd : Differentiable ℂ f := by
    refine hv.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
    simp only [hermForm, dotProduct]
    fun_prop
  have hperf : ∀ y, ∀ a ∈ lat, ‖f (y + a)‖ = ‖f y‖ := by
    intro y a ha
    have e1 : f (y + a) = (v y * Complex.exp ((c : ℂ) * hermForm Hm y x)) *
        (Complex.exp (-((c : ℂ) * hermForm Hm x a)) * Complex.exp ((c : ℂ) * hermForm Hm a x)) := by
      simp only [hf, hper y a ha, hlin, mul_add, Complex.exp_add]
      ring
    rw [e1, norm_mul, norm_exp_neg_hermForm_mul_exp_hermForm_eq_one Hm herm c x a, _root_.mul_one]

  obtain ⟨s, hsl, hss, hli⟩ := exists_linearIndependent ℝ (lat : Set (Fin g → ℂ))
  rw [span] at hss
  let b : Module.Basis s ℝ (Fin g → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hss.ge)
  have : Finite s := Module.Finite.finite_basis b
  letI : Fintype s := Fintype.ofFinite s
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (ZSpan.fundamentalDomain_isBounded b).closure
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hfd.continuous.continuousOn
  have hmem : ∀ y, y - ZSpan.fract b y ∈ lat := by
    intro y
    rw [ZSpan.fract_apply, sub_sub_cancel]
    have h1 : Submodule.span ℤ (Set.range b) ≤ lat.toIntSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa [b, Module.Basis.mk_apply] using hsl i.2
    exact h1 (ZSpan.floor b y).2
  have hbd : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h2 := hperf (ZSpan.fract b y) _ (hmem y)
    rw [add_sub_cancel] at h2
    rw [h2]
    exact hM _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b y))
  have h0 := hfd.apply_eq_apply_of_bounded hbd z 0
  have hz0 : hermForm Hm 0 x = 0 := by simp [hermForm]
  simp only [hf, hz0, mul_zero, Complex.exp_zero, _root_.mul_one] at h0
  rw [← h0, _root_.mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, _root_.mul_one]

private theorem fac_zpow_mul_fac_add_zpow_neg_eq_exp {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (k : ℤ) (x : Fin g → ℂ) {a : Fin g → ℂ} (ha : a ∈ Φ.lat) (z : Fin g → ℂ) :
    Φ.fac a z ^ k * Φ.fac a (x + z) ^ (-k) = Complex.exp (-((k : ℂ) * Real.pi * hermForm Φ.Hm x a)) := by
  have hχ : Φ.χ a ≠ 0 := by
    intro h
    have h1 := Φ.χ_norm a ha
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hne : Φ.fac a (x + z) ≠ 0 := mul_ne_zero hχ (Complex.exp_ne_zero _)
  have hq : Φ.fac a z = Φ.fac a (x + z) * Complex.exp (-((Real.pi : ℂ) * hermForm Φ.Hm x a)) := by
    simp only [AnFr.fac, hermForm, add_dotProduct]
    rw [_root_.mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hq, mul_zpow, zpow_neg, mul_comm (Φ.fac a (x + z) ^ k), _root_.mul_assoc,
    mul_inv_cancel₀ (zpow_ne_zero _ hne), _root_.mul_one, ← Complex.exp_int_mul]
  congr 1
  ring

theorem exists_thConst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ), U.pt = Φ.e x → ∃ c : ℂ, c ≠ 0 ∧ Φ.ThConst k U x c := by
  intro S A _ _ L x0 g Φ k U x hU

  have hs : ∀ t : Over.mk x0 ⟶ A, ptSecT A t ≫ snd (Over.mk x0) A = t := by
    intro t
    simp [ptSecT]
  have ht : ∀ t : Over.mk x0 ⟶ A, ptSecT A t ≫ translPt A U.pt = U.pt * t := by
    intro t
    simp only [ptSecT, translPt, Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, Category.id_comp]
  have hh : IsHolFam (g := g) (fun z => (ptSecT A (Φ.e z)).left) := by
    have h := isHolFam_pullback_lift S (Over.mk x0).left A.left (Over.mk x0).hom A.hom g (fun _ => 𝟙 _)
      (fun z => (Φ.e z).left) x0 (fun _ => Category.id_comp _) (fun z => Over.w (Φ.e z))
      (isHolFam_const (g := g) _) Φ.hol
    exact h
  have hdiff : ∀ i : Fin 2, Differentiable ℂ ((![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i) :=
    Fin.forall_fin_two.2 ⟨differentiable_id, (differentiable_const x).add differentiable_id⟩
  have hq : ∀ (z : Fin g → ℂ) (i : Fin 2), (ptSecT A (Φ.e z)).left ≫
      (![(snd (Over.mk x0) A).left, (translPt A U.pt).left] : Fin 2 → _) i =
      (Φ.e ((![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i z)).left := by
    intro z
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A).left = (Φ.e z).left
      rw [← Over.comp_left, hs]
    · show (ptSecT A (Φ.e z)).left ≫ (translPt A U.pt).left = (Φ.e (x + z)).left
      rw [← Over.comp_left, ht, hU, Φ.e_add]

  obtain ⟨v, hvd, hv0, hvR, -, hvP⟩ := GlobalTheory.AnValGenRd.exists_reading S A L x0 g Φ (Over.mk x0 ⊗ A).left (Fin 2)
    ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] ![k, -k] U.φ U.isGen g
    (fun z => (ptSecT A (Φ.e z)).left) ![fun z => z, fun z => x + z] hh hdiff hq
  have hper : ∀ z, ∀ a ∈ Φ.lat, v (z + a) = v z * Complex.exp (-((k : ℂ) * Real.pi * hermForm Φ.Hm x a)) := by
    intro z a ha
    have hqa : (ptSecT A (Φ.e (z + a))).left = (ptSecT A (Φ.e z)).left := by
      rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]
    have h := hvP z (z + a) (fun _ => a) hqa (Fin.forall_fin_two.2 ⟨⟨ha, rfl⟩, ⟨ha, (add_assoc x z a).symm⟩⟩)
    rw [Fin.prod_univ_two] at h
    rw [h, ← fac_zpow_mul_fac_add_zpow_neg_eq_exp Φ k x ha z]
    rfl
  refine ⟨v 0 * Complex.exp ((k : ℂ) * Real.pi * hermForm Φ.Hm x x / 2),
    mul_ne_zero (hv0 0) (Complex.exp_ne_zero _), hU, fun z => ?_⟩
  have hvz : v 0 * Complex.exp ((k : ℂ) * Real.pi * hermForm Φ.Hm x x / 2) * fock Φ.Hm k x (fun _ => 1) z = v z := by
    rw [thConst_liouville Φ.lat Φ.span Φ.Hm Φ.herm k x v hvd hper z]
    simp only [fock, _root_.mul_one]
    rw [_root_.mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hp : (fun i : Fin 2 => (![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i z) = ![z, x + z] := by
    funext i
    fin_cases i <;> rfl
  have hR := hvR z
  rw [hp] at hR
  rw [hvz]
  exact hR

end GlobalTheory.AnVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstantPowEqOneOfPowerTrivial
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValThPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem telescope (c h : ℂ) (k : ℤ) (f : ℕ → ℂ) (hf : ∀ i, f i ≠ 0) (n : ℕ) :
    ∏ i ∈ Finset.range n, (c * Complex.exp (-((k : ℂ) * Real.pi * (i * h)) - (k : ℂ) * Real.pi * h / 2) *
      (f i ^ k * f (i + 1) ^ (-k))) =
      c ^ n * Complex.exp (-((k : ℂ) * (Real.pi / 2 * (n * n * h)))) * (f 0 ^ k * f n ^ (-k)) := by
  induction n with
  | zero => simp [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero k (hf 0))]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, pow_succ]
    have h1 : f n ^ (-k) * f n ^ k = 1 := by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero k (hf n))]
    have h2 : Complex.exp (-((k : ℂ) * (Real.pi / 2 * (n * n * h)))) *
        Complex.exp (-((k : ℂ) * Real.pi * (n * h)) - (k : ℂ) * Real.pi * h / 2) =
        Complex.exp (-((k : ℂ) * (Real.pi / 2 * (((n + 1 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * h)))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← h2]
    linear_combination (c ^ n * c * Complex.exp (-((k : ℂ) * (Real.pi / 2 * (n * n * h)))) *
        Complex.exp (-((k : ℂ) * Real.pi * (n * h)) - (k : ℂ) * Real.pi * h / 2) *
        (f 0 ^ k * f (n + 1) ^ (-k))) * h1

theorem herm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (a • z) w = a * hermForm Hm z w := by unfold hermForm; rw [smul_dotProduct, smul_eq_mul]

theorem herm_nat_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℕ) (z w : Fin g → ℂ) :
    hermForm Hm z ((a : ℂ) • w) = a * hermForm Hm z w := by unfold hermForm; rw [star_smul, star_natCast, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem translPt_mul (x : T ⟶ A) : translPt A x = (fst T A ≫ x) * snd T A := rfl

theorem translT_snd (y : T ⟶ A) : translT A y ≫ snd T A = translPt A y := by unfold translT; exact lift_snd _ _

theorem translT_translPt [IsCommMonObj A] (x y : T ⟶ A) :
    translT A y ≫ translPt A x = translPt A (x * y) := by
  have hf : translT A y ≫ fst T A = fst T A := by unfold translT; exact lift_fst _ _
  rw [translPt_mul, translPt_mul, comp_mul, ← Category.assoc, hf, translT_snd, translPt_mul, comp_mul, _root_.mul_assoc]

theorem pt_translPt (x z : T ⟶ A) : ptSecT A z ≫ translPt A x = x * z := by
  unfold ptSecT translPt
  rw [comp_lift_assoc, lift_fst_assoc, Category.id_comp, lift_snd]
  rfl

theorem pt_translT (x z : T ⟶ A) : ptSecT A z ≫ translT A x = ptSecT A (x * z) := by
  have h := pt_translPt A x z
  unfold ptSecT at h ⊢
  unfold translT
  rw [comp_lift, lift_fst, h]

theorem powφ_zero (x : T ⟶ A) (n : ℕ) (i : Fin n) : powφ A x n (i, 0) = (translPt A (x ^ (i : ℕ))).left := by
  unfold powφ
  dsimp only
  rw [Matrix.cons_val_zero, ← Over.comp_left, translT_snd]

theorem powφ_one [IsCommMonObj A] (x : T ⟶ A) (n : ℕ) (i : Fin n) :
    powφ A x n (i, 1) = (translPt A (x ^ ((i : ℕ) + 1))).left := by
  unfold powφ
  dsimp only
  rw [Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left, translT_translPt, ← pow_succ']

private theorem isChart_choose_and_symm_apply (L : LB A.left) (k : ℤ) (θ : ThetaGrp A L k T) (n : ℕ) (q : Sp ℂ ⟶ (T ⊗ A).left)
    (j : Fin n × Fin 2 → L.ι) (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (powφ A θ.pt n) j) (i : Fin n) :
    ⊤ ≤ (q ≫ (translT A (θ.pt ^ (i : ℕ))).left) ⁻¹ᵁ
      LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] (fun b => j (i, b)) := by
  intro p _
  have hp := hj (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  unfold LB.wchart at hp ⊢
  unfold powφ at hp
  simp at hp ⊢
  exact hp i

private theorem exists_unit_mul_eq_mul_uniformizer_pow {Z Y : Scheme.{0}} (q : Sp ℂ ⟶ Z) (ψ : Z ⟶ Y) (V : Y.Opens) {W W' : Z.Opens}
    (e1 : W ≤ W') (e2 : W' ≤ ψ ⁻¹ᵁ V) (h : ⊤ ≤ q ⁻¹ᵁ W) (h' : ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ V) (u : Γ(Y, V)) :
    (q.appLE W ⊤ h).hom ((Z.presheaf.map (homOfLE e1).op).hom ((Z.presheaf.map (homOfLE e2).op).hom
      ((ψ.app V).hom u))) = ((q ≫ ψ).appLE V ⊤ h').hom u := by
  have key : Z.presheaf.map (homOfLE e2).op ≫ Z.presheaf.map (homOfLE e1).op ≫ q.appLE W ⊤ h =
      q.appLE (ψ ⁻¹ᵁ V) ⊤ h' := by
    simp only [Scheme.Hom.map_appLE]
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ← key]
  rfl

private theorem valAt'_prod_res_pullU_eq_prod {Z Y : Scheme.{0}} {n : ℕ} (q : Sp ℂ ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ q ⁻¹ᵁ W)
    (ψ : Fin n → (Z ⟶ Y)) (V : Fin n → Y.Opens) (W' : Fin n → Z.Opens) (e1 : ∀ i, W ≤ W' i)
    (e2 : ∀ i, W' i ≤ ψ i ⁻¹ᵁ V i) (u : ∀ i, Γ(Y, V i)ˣ) (h' : ∀ i, ⊤ ≤ (q ≫ ψ i) ⁻¹ᵁ V i) :
    valAt' q W (∏ i, res (e1 i) (res (e2 i) (pullU (ψ i) (V i) (u i)))).val =
      ∏ i, valAt' (q ≫ ψ i) (V i) (u i).val := by
  unfold valAt'
  rw [dif_pos h]
  simp only [dif_pos (h' _)]
  unfold valAt res pullU
  simp only [Units.coe_prod, map_prod, Units.coe_map, MonoidHom.coe_coe]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [exists_unit_mul_eq_mul_uniformizer_pow q (ψ i) (V i) (e1 i) (e2 i) h (h' i)]

theorem val_powGen (L : LB A.left) (k : ℤ) (θ : ThetaGrp A L k T) (n : ℕ) (q : Sp ℂ ⟶ (T ⊗ A).left)
    (j : Fin n × Fin 2 → L.ι) (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (powφ A θ.pt n) j) :
    valAt' q (LB.wchart L (powφ A θ.pt n) j) ((powGen A L k θ n).s j).val =
      ∏ i : Fin n, valAt' (q ≫ (translT A (θ.pt ^ (i : ℕ))).left)
        (LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] (fun b => j (i, b)))
        (θ.φ.s (fun b => j (i, b))).val := by
  unfold powGen LB.pullGen
  exact valAt'_prod_res_pullU_eq_prod q _ hj _ _ _ _ _ _ (fun i => isChart_choose_and_symm_apply A L k θ n q j hj i)

end

theorem e_nat {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
    (x : Fin g → ℂ) (i : ℕ) : Φ.e ((i : ℂ) • x) = Φ.e x ^ i := by
  induction i with
  | zero => simpa using (Φ.e_ker 0).mpr Φ.lat.zero_mem
  | succ i ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

theorem thConst_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ), Φ.ThConst k U x c → (n : ℂ) • x ∈ Φ.lat → LB.Gen.Corr L.L _ _ _ _ (powGen A L.L k U n) (LB.oneGen L.L) → c ^ n * Φ.χ ((n : ℂ) • x) ^ k = 1 := by
  intro S A _ _ L x0 g Φ k n U x c hT hx hC
  obtain ⟨hpt, hrd⟩ := hT
  have he0 : Φ.e 0 = 1 := (Φ.e_ker 0).mpr Φ.lat.zero_mem
  have hpts : ∀ m : ℕ, (ptSecT A (Φ.e 0)).left ≫ (translPt A (U.pt ^ m)).left = (Φ.e ((m : ℂ) • x)).left := by
    intro m
    rw [← Over.comp_left, pt_translPt, he0, _root_.mul_one, hpt, ← e_nat]
  have hptT : ∀ m : ℕ, (ptSecT A (Φ.e 0)).left ≫ (translT A (U.pt ^ m)).left =
      (ptSecT A (Φ.e ((m : ℂ) • x))).left := by
    intro m
    rw [← Over.comp_left, pt_translT, he0, _root_.mul_one, hpt, ← e_nat]
  have hs : ∀ m : ℕ, (((m + 1 : ℕ)) : ℂ) • x = x + (m : ℂ) • x := by
    intro m; push_cast; rw [add_smul, one_smul, add_comm]
  have hG : Φ.GenRd (powφ A U.pt n) _ (powGen A L.L k U n) (ptSecT A (Φ.e 0)).left
      (fun p => ![((p.1 : ℕ) : ℂ) • x, x + ((p.1 : ℕ) : ℂ) • x] p.2)
      (∏ i : Fin n, c * fock Φ.Hm k x (fun _ => 1) (((i : ℕ) : ℂ) • x)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨i, b⟩
      rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
      · rw [powφ_zero, hpts]; rfl
      · rw [powφ_one, hpts, hs]; rfl
    · intro j hj
      rw [val_powGen A L.L k U n _ j hj, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hc := isChart_choose_and_symm_apply A L.L k U n _ j hj i
      rw [hptT] at hc ⊢
      exact (hrd (((i : ℕ) : ℂ) • x)).2 _ hc
  have h1 : Φ.GenRd _ _ (LB.oneGen L.L) (ptSecT A (Φ.e 0)).left (fun e => e.elim) 1 := by
    refine ⟨fun kk => kk.elim, fun j' hj' => ?_⟩
    unfold valAt'
    rw [dif_pos hj']
    unfold valAt LB.oneGen
    simp only [Units.val_one, Fintype.prod_empty, _root_.mul_one]
    exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (map_one _)).trans (map_one _)
  obtain ⟨J, hJ, heq⟩ := (GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG h1).1 hC
  simp only [Fintype.prod_empty, _root_.one_mul] at heq
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → ℂ, f = fun m : ℕ => Φ.fr (J (translPt A (U.pt ^ m)).left) ((m : ℂ) • x) := ⟨_, rfl⟩
  have hf : ∀ m, f m ≠ 0 := by
    intro m
    rw [hfdef]
    have hc := hJ (translPt A (U.pt ^ m)).left
    rw [hpts m] at hc
    exact Φ.fr_ne _ _ hc
  have key : ∏ i ∈ Finset.range n, (c * Complex.exp (-((k : ℂ) * Real.pi * (i * hermForm Φ.Hm x x)) -
      (k : ℂ) * Real.pi * hermForm Φ.Hm x x / 2) * (f i ^ k * f (i + 1) ^ (-k))) = 1 := by
    refine Eq.trans ?_ heq
    rw [Finset.prod_range, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_two, powφ_zero, powφ_one, hfdef]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fock, herm_smul_left, hs,
      _root_.mul_one, powε]
  rw [telescope c (hermForm Φ.Hm x x) k f hf n] at key
  have hpn : U.pt ^ n = U.pt ^ 0 := by rw [pow_zero, hpt, ← e_nat, (Φ.e_ker _).mpr hx]
  have hc0 := hJ (translPt A (U.pt ^ 0)).left
  rw [hpts 0] at hc0
  simp only [Nat.cast_zero, zero_smul] at hc0
  have hper := Φ.fr_per _ hx _ 0 hc0
  have h0 : hermForm Φ.Hm 0 ((n : ℂ) • x) = 0 := by simp [hermForm]
  simp only [h0, mul_zero, zero_add] at hper
  have hfn := hf n
  rw [hfdef] at key hfn
  simp only [hpn, Nat.cast_zero, zero_smul] at key hfn
  rw [hper, mul_zpow, mul_zpow] at key
  have hB : Complex.exp (-((k : ℂ) * (Real.pi / 2 * ((n : ℂ) * (n : ℂ) * hermForm Φ.Hm x x)))) *
      Complex.exp (Real.pi / 2 * hermForm Φ.Hm ((n : ℂ) • x) ((n : ℂ) • x)) ^ k = 1 := by
    rw [← Complex.exp_int_mul, ← Complex.exp_add, herm_smul_left, herm_nat_right, ← Complex.exp_zero]
    congr 1
    ring
  have hnk : Φ.fr (J (translPt A (U.pt ^ 0)).left) ((n : ℂ) • x) ^ k *
      Φ.fr (J (translPt A (U.pt ^ 0)).left) ((n : ℂ) • x) ^ (-k) = 1 := by
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hfn)]
  linear_combination key - c ^ n * Φ.χ ((n : ℂ) • x) ^ k *
    Complex.exp (-((k : ℂ) * (Real.pi / 2 * ((n : ℂ) * (n : ℂ) * hermForm Φ.Hm x x)))) *
    Complex.exp (Real.pi / 2 * hermForm Φ.Hm ((n : ℂ) • x) ((n : ℂ) • x)) ^ k * hnk -
    c ^ n * Φ.χ ((n : ℂ) • x) ^ k * hB

end GlobalTheory.AnValThPow
end
end

