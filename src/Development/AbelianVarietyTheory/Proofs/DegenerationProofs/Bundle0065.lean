module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsDualThetaTestLatticeBound
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH
namespace MinorTest

theorem exists_norm_between {C : Type*} [NontriviallyNormedField C] [IsAlgClosed C] {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) : ∃ x : C, a < ‖x‖ ∧ ‖x‖ < b := by
  have hb : 0 < b := ha.trans_lt hab
  have hr : a / b < 1 := (div_lt_one hb).2 hab
  have hr0 : 0 ≤ a / b := div_nonneg ha hb.le
  obtain ⟨z, hz1, hz2⟩ : ∃ z : C, a / b < ‖z‖ ∧ ‖z‖ < 1 := by
    obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one C
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).eventually_lt_const hy0
    obtain ⟨n, hn, hn1⟩ := (h.and (Filter.eventually_gt_atTop 0)).exists
    obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq y hn1
    rw [norm_pow] at hn hy1
    exact ⟨x, lt_of_pow_lt_pow_left₀ n (norm_nonneg x) hn,
      (pow_lt_one_iff_of_nonneg (norm_nonneg x) hn1.ne').1 hy1⟩
  have hz0 : 0 < ‖z‖ := hr0.trans_lt hz1
  have hy : 1 < ‖z‖⁻¹ := (one_lt_inv₀ hz0).2 hz2
  obtain ⟨n, h1, h2⟩ := exists_mem_Ioc_zpow hb hy
  refine ⟨z⁻¹ ^ n, ?_, ?_⟩
  · rw [norm_zpow, norm_inv]
    rw [zpow_add_one₀ (inv_pos.2 hz0).ne', ← div_eq_mul_inv, le_div_iff₀ hz0] at h2
    rw [div_lt_iff₀ hb, mul_comm] at hz1
    exact hz1.trans_le h2
  · rwa [norm_zpow, norm_inv]

theorem norm_det_le_pow {C J : Type*} [NormedField C] [IsUltrametricDist C] [Fintype J] [DecidableEq J]
    (A : Matrix J J C) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ∀ i j, ‖A i j‖ ≤ ρ) :
    ‖A.det‖ ≤ ρ ^ Fintype.card J := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun σ _ => ?_
  have hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : C)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, hs, _root_.one_mul, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _

theorem norm_det_le_of_comb {C J I : Type*} [NormedField C] [IsUltrametricDist C] [Fintype J]
    [DecidableEq J] [Fintype I] (g : I → J → C) (c : J → I → C) (hc : ∀ i m, ‖c i m‖ ≤ 1) {ν : ℝ}
    (hν : 0 ≤ ν) (h : ∀ k : J → I, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ν) :
    ‖Matrix.det (Matrix.of fun i => ∑ m, c i m • g m)‖ ≤ ν := by
  have e : Matrix.det (Matrix.of fun i => ∑ m, c i m • g m) =
      ∑ k : J → I, (∏ i, c i (k i)) • Matrix.det (Matrix.of fun i j => g (k i) j) := by
    have := (Matrix.detRowAlternating (n := J) (R := C)).toMultilinearMap.map_sum
      (fun i m => c i m • g m)
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    exact (Matrix.detRowAlternating (n := J) (R := C)).toMultilinearMap.map_smul_univ
      (fun i => c i (k i)) (fun i => g (k i))
  rw [e]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hν fun k _ => ?_
  rw [smul_eq_mul, norm_mul, norm_prod]
  calc _ ≤ 1 * ν := mul_le_mul (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hc _ _) (h k)
        (norm_nonneg _) zero_le_one
    _ = ν := _root_.one_mul _

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (h : Filter.Tendsto q Filter.cofinite Filter.atTop) {x : X} (hx0 : x ≠ 0) : 0 < q x := by
  by_contra hx
  push_neg at hx
  have hfin : {v | ¬ (0 : ℝ) < q v}.Finite := Filter.eventually_cofinite.1 (h.eventually_gt_atTop 0)
  have hinj : Function.Injective fun n : ℕ => ((n : ℤ) + 1) • x := by
    intro a b hab
    have := smul_left_injective ℤ hx0 hab
    omega
  refine Set.infinite_of_injective_forall_mem hinj (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  refine mul_nonpos_of_nonneg_of_nonpos ?_ hx
  positivity

theorem exists_eStd_eq (g n : ℕ) (φ : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n) :
    ∃ a, ∀ b, eStd g n a b = φ b := by
  let ψ : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n := φ.toZModLinearMap n
  refine ⟨Sum.elim (fun i => φ (Pi.single (.inr i) 1)) (fun i => -φ (Pi.single (.inl i) 1)), fun b => ?_⟩
  have hb : φ b = ∑ s, b s * φ (Pi.single s 1) := by
    change ψ b = ∑ s, b s * ψ (Pi.single s 1)
    conv_lhs => rw [pi_eq_sum_univ' b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
  rw [hb, Fintype.sum_sum_type, ← Finset.sum_add_distrib, eStd]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem subsingleton_of_perp_eq_bot (τ : S.Test p y₀) (h : S.perp τ.yy.ker = ⊥) (x : τ.X) : x = 0 := by
  have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
  haveI : Fact (1 < S.r * S.N) := ⟨h2⟩
  let b := Module.Free.chooseBasis ℤ τ.X
  haveI : IsEmpty (Module.Free.ChooseBasisIndex ℤ τ.X) := by
    refine ⟨fun i => ?_⟩
    let f : τ.X →+ ZMod (S.r * S.N) := (Int.castAddHom _).comp (b.coord i).toAddMonoidHom
    let f' : τ.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : τ.X →+ τ.X).range →+ ZMod (S.r * S.N) :=
      QuotientAddGroup.lift _ f (by
        rintro _ ⟨v, rfl⟩
        rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, map_nsmul, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul])
    obtain ⟨a, ha⟩ := exists_eStd_eq _ _ (f'.comp τ.yy)
    have hm : a ∈ S.perp τ.yy.ker := fun u hu => by
      rw [ha, AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 hu, map_zero]
    rw [h, AddSubgroup.mem_bot] at hm
    obtain ⟨u, hu⟩ := τ.yy_onto (QuotientAddGroup.mk (b i))
    have := ha u
    rw [hm, AddMonoidHom.comp_apply, hu] at this
    simp [eStd, f', f] at this
  exact b.repr.injective (Subsingleton.elim _ _)

theorem eq_bot_of_char {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (h : ∀ c : T →+ ZMod S.N, c = 0) :
    T = ⊥ := by
  obtain ⟨-, d, ⟨e⟩⟩ := hT
  haveI : Fact (1 < S.N) := ⟨S.N_ge⟩
  haveI : IsEmpty (Fin d) := by
    refine ⟨fun i => ?_⟩
    have := DFunLike.congr_fun (h ((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
      ((Pi.evalAddMonoidHom (fun _ : Fin d => ZMod (S.r * S.N)) i).comp e.toAddMonoidHom)))
      (e.symm (fun _ => 1))
    simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
      AddEquiv.apply_symm_apply, Pi.evalAddMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe, map_one,
      AddMonoidHom.zero_apply] at this
    exact one_ne_zero this
  rw [eq_bot_iff]
  intro t ht
  have : (⟨t, ht⟩ : T) = 0 := e.injective (Subsingleton.elim _ _)
  exact congrArg Subtype.val this

end MinorTest

open MinorTest in
theorem minors_dual_testLattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → ∀ (n : ℕ) (ρ₀ : ℝ) (g : Fin n → S.J → PadicAlgCl p), 0 < ρ₀ → (∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range g) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ ρ₀) → (∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J) ∧ ((∃ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ = ρ₀ ^ Fintype.card S.J) ↔ S.perp τ.yy.ker = ⊥) := by
  intro o Ω _ _ _ _ S p _ y₀ τ hint _ n ρ₀ g hρ hg
  obtain ⟨B, l, α, -, hdet, -, hl, hall, -, hE⟩ := exists_adapted_basis_testLattice o Ω S p y₀ τ hint
  have hN : (0 : ℝ) < S.N := by exact_mod_cast lt_of_lt_of_le two_pos S.N_ge
  have hq : ∀ x, 0 ≤ τ.q x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (pos_of_tendsto τ.q τ.pos hx).le
  have hl1 : ∀ i, 1 ≤ ‖l i‖ := fun i => by
    rw [hl]; exact Real.one_le_exp (div_nonneg (hq _) hN.le)
  set M : Matrix S.J S.J (PadicAlgCl p) := Matrix.of fun i j => l i * B i j with hM
  have hMdet : ‖M.det‖ = ∏ i, ‖l i‖ := by
    rw [hM, Matrix.det_mul_column, norm_mul, hdet, _root_.mul_one, norm_prod]
  have hM1 : 1 ≤ ‖M.det‖ := by
    rw [hMdet]; exact Finset.prod_induction _ (1 ≤ ·) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun i _ => hl1 i
  have key : ∀ k : S.J → Fin n,
      ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ * ‖M.det‖ ≤ ρ₀ ^ Fintype.card S.J := fun k => by
    rw [← Matrix.det_transpose M, ← norm_mul, ← Matrix.det_mul]
    refine norm_det_le_pow _ hρ.le fun i j => ?_
    exact (hg (g (k i))).1 (Submodule.subset_span ⟨_, rfl⟩) (fun t => l j * B j t)
      (hE ▸ Submodule.subset_span ⟨j, rfl⟩)
  have h1 : ∀ k : S.J → Fin n,
      ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J := fun k =>
    (le_mul_of_one_le_right (norm_nonneg _) hM1).trans (key k)
  have hρd : 0 < ρ₀ ^ Fintype.card S.J := pow_pos hρ _
  refine ⟨h1, ⟨?_, fun hbot => ?_⟩⟩
  · rintro ⟨k, hk⟩
    have h2 := key k
    rw [hk, mul_le_iff_le_one_right hρd, hMdet] at h2
    refine eq_bot_of_char τ.isoFree fun c => ?_
    obtain ⟨i, rfl⟩ := hall c
    have h3 : ‖l i‖ ≤ 1 := by
      refine le_trans ?_ h2
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      refine le_mul_of_one_le_right (norm_nonneg _) ?_
      exact Finset.prod_induction _ (1 ≤ ·) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun i _ => hl1 i
    have h4 : α i = 0 := by
      by_contra hne
      have := Real.one_lt_exp_iff.2 (div_pos (pos_of_tendsto τ.q τ.pos hne) hN)
      rw [hl] at h3
      linarith
    rw [h4, map_zero]
  · have hMe : ‖M.det‖ = 1 := by
      rw [hMdet]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hl, subsingleton_of_perp_eq_bot τ hbot (α i)]
      simp
    have hMu : IsUnit M.det := by
      rw [isUnit_iff_ne_zero, ← norm_ne_zero_iff, hMe]; exact one_ne_zero
    by_contra hne
    push_neg at hne
    obtain ⟨ν, hν0, hν1, hν2⟩ : ∃ ν : ℝ, 0 ≤ ν ∧ ν < ρ₀ ^ Fintype.card S.J ∧
        ∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ν := by
      rcases isEmpty_or_nonempty (S.J → Fin n) with he | he
      · exact ⟨0, le_rfl, hρd, fun k => he.elim k⟩
      · obtain ⟨k₀, hk₀⟩ := Finite.exists_max
          fun k : S.J → Fin n => ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖
        exact ⟨_, norm_nonneg _, lt_of_le_of_ne (h1 k₀) (hne k₀), hk₀⟩
    obtain ⟨x, hx1, hx2⟩ := exists_norm_between (C := PadicAlgCl p) hν0 hν1
    obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq x (Fintype.card_pos (α := S.J))
    have hz : ‖z‖ ≤ ρ₀ := by
      rw [norm_pow] at hx2
      exact (lt_of_pow_lt_pow_left₀ _ hρ.le hx2).le
    set W : Matrix S.J S.J (PadicAlgCl p) := z • (M.transpose)⁻¹ with hW
    have hWM : W * M.transpose = z • (1 : Matrix S.J S.J (PadicAlgCl p)) := by
      rw [hW, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose])]
    have hWdet : ‖W.det‖ = ‖z ^ Fintype.card S.J‖ := by
      have := congrArg (fun A => ‖Matrix.det A‖) hWM
      simpa only [Matrix.det_mul, Matrix.det_transpose, norm_mul, hMe, _root_.mul_one, Matrix.det_smul,
        Matrix.det_one] using this
    have hmem : ∀ i, W i ∈ Submodule.span (OO p) (Set.range g) := fun i => by
      rw [hg, hE]
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        have : W i ⬝ᵥ (fun t => l j * B j t) = (W * M.transpose) i j := rfl
        rw [this, hWM, Matrix.smul_apply, Matrix.one_apply]
        split_ifs
        · simpa using hz
        · simpa using hρ.le
      | zero => simpa using hρ.le
      | add u v _ _ hu hv =>
        rw [dotProduct_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
      | smul a v _ hv =>
        have : a • v = (a : PadicAlgCl p) • v := rfl
        rw [this, dotProduct_smul, smul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_OO_iff _).1 a.2)).trans hv
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (hmem i)
    have h5 := norm_det_le_of_comb g (fun i m => (c i m : PadicAlgCl p))
      (fun i m => (mem_OO_iff _).1 (c i m).2) hν0 hν2
    have h6 : (Matrix.of fun i => ∑ m, (c i m : PadicAlgCl p) • g m) = W := by
      ext i j
      exact congrFun (hc i) j
    rw [h6, hWdet] at h5
    linarith
end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PreUniformisationComparisonTorusInvariant
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory

namespace PreTorusInvariance

theorem cube_alg {V : Type} [CommGroup V] {A : Type} [CommGroup A] {a W W' d : A → V} (h : ∀ x, a x * W' x = W x * d x)
    {x y u : A} {C C' c c' : V}
    (h₁ : C * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * c)
    (h₂ : C' * W' (x * y) * W' (x * u) * W' (y * u) * W' 1 = W' (x * y * u) * W' x * W' y * W' u * c')
    (h₃ : c * d (x * y) * d (x * u) * d (y * u) * d 1 = d (x * y * u) * d x * d y * d u * c') :
    C = a (x * y * u) * (a (x * y))⁻¹ * (a (x * u))⁻¹ * (a (y * u))⁻¹ * a x * a y * a u * (a 1)⁻¹ * C' := by
  have E := fun {p q : V} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E h₁; have a₂ := E h₂; have a₃ := E h₃
  have b₁ := E (h (x * y * u)); have b₂ := E (h (x * y)); have b₃ := E (h (x * u)); have b₄ := E (h (y * u))
  have b₅ := E (h x); have b₆ := E (h y); have b₇ := E (h u); have b₈ := E (h 1)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - b₁ + b₂ + b₃ + b₄ - b₅ - b₆ - b₇ + b₈

theorem even_alg {V : Type} [CommGroup V] {A : Type} [CommGroup A] {a W W' d : A → V} (h : ∀ x, a x * W' x = W x * d x)
    {x : A} {s s' c c' : V} (h₁ : s * W x = W x⁻¹ * c) (h₂ : s' * W' x = W' x⁻¹ * c') (h₃ : c * d x = d x⁻¹ * c') :
    s * a x = a x⁻¹ * s' := by
  have E := fun {p q : V} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E h₁; have a₂ := E h₂; have a₃ := E h₃
  have b₁ := E (h x); have b₂ := E (h x⁻¹)
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ + b₁ - b₂

theorem vals_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P P' : CP G}
    {w : LB.Iso P'.L.L (P.L.L.pull (𝟙 G.left))} {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}
    (h : IsCPMap P' P (𝟙 _) (𝟙 G.left) hw w) {T : Over S} {z : T.left} {N N'} (hN : Good P.L.L z N)
    (hN' : Good P'.L.L z N') (d : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ)
    (hd : ∀ x, d x = gw w x.left z (N x.left) (N' x.left)) {B : Type} [CommGroup B] (β : B →* (T ⟶ G)) :
    (∀ x, val P.sym (β x).left z N * d (β x) = d (β x⁻¹) * val P'.sym (β x).left z N') ∧
    ∀ x y u, cubV P.c z N (β x) (β y) (β u) * d (β (x * y)) * d (β (x * u)) * d (β (y * u)) * d (β 1) =
      d (β (x * y * u)) * d (β x) * d (β y) * d (β u) * cubV P'.c z N' (β x) (β y) (β u) := by
  obtain ⟨-, s, c⟩ := h.vals T z N' N hN' hN d (fun x => by rw [hd, Category.comp_id])
  refine ⟨fun x => ?_, fun x y u => ?_⟩
  · have s := s (β x)
    rwa [Category.comp_id, ← map_inv] at s
  · have c := c (β x) (β y) (β u)
    rw [_root_.id, cubV_toBase_id] at c
    simp only [map_mul, map_one]
    exact c

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {e : ℕ} {D D' : DegPre R} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {U : PreU I D A G} {U' : PreU I D' A' G}

def cubP (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (x y u : T ⟶ thickObj R I e G) : (T.left.presheaf.stalk z)ˣ :=
  cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
    ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map y ≫ g.pG)
    ((Over.map (thick R I e)).map u ≫ g.pG)

theorem cubP_congr (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) {a b a' b' : T ⟶ thickObj R I e G} (c : T ⟶ thickObj R I e G)
    (ha : a ≫ g.q = a' ≫ g.q) (hb : b ≫ g.q = b' ≫ g.q) : cubP g z J a b c = cubP g z J a' b' c := by
  have k : ∀ {a a' : T ⟶ thickObj R I e G}, a ≫ g.q = a' ≫ g.q →
      (Over.map (thick R I e)).map a ≫ g.pG = (Over.map (thick R I e)).map a' ≫ g.pG := fun h =>
    Over.OverMorphism.ext (TorusInvariance.pG_congr g h)
  unfold cubP
  rw [k ha, k hb]

theorem vals (u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left))
    {wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))} {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}
    (hL : IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι)
      (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM →
      (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL →
      (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' →
      gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL')
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι}
    {J' : (T.left ⟶ D'.P.A.left) → D'.P.L.ι} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (a : (T.left ⟶ (thickObj R I e G).left) → (T.left.presheaf.stalk z)ˣ)
    (ha : ∀ r, a r = gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left))) :
    (∀ x : T ⟶ thickObj R I e G, val D.sym (x.left ≫ (U.gt e).pG.left) z J * a x.left =
      a (x⁻¹).left * val D'.sym (x.left ≫ (U'.gt e).pG.left) z J') ∧
    ∀ x y v : T ⟶ thickObj R I e G, cubP (U.gt e) z J x y v =
      a (x * y * v).left * (a (x * y).left)⁻¹ * (a (x * v).left)⁻¹ * (a (y * v).left)⁻¹ * a x.left * a y.left *
        a v.left * (a (1 : T ⟶ thickObj R I e G).left)⁻¹ * cubP (U'.gt e) z J' x y v := by
  obtain ⟨N, hN⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨N', hN'⟩ := exists_good_pt U'.P.L.isLB z
  obtain ⟨W, hW⟩ : ∃ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W x =
    gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => N (x.left ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W x =
    gw (U'.w e) x.left z (J' (x.left ≫ (U'.gt e).pG.left)) (fun _ => N' (x.left ≫ (fstG I e G).left)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ((Over.map (thick R I e)).obj T ⟶ G) → (T.left.presheaf.stalk z)ˣ, ∀ x, d x =
    gw wL x.left z (N x.left) (N' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨-, s₁, c₁⟩ := U.w_vals e T z N J hN hJ W hW
  obtain ⟨-, s₂, c₂⟩ := U'.w_vals e T z N' J' hN' hJ' W' hW'
  let β : (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
    MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
      toBase_mul_pullback G (thick R I e) T x y
  obtain ⟨s₃, c₃⟩ := vals_id hL (T := (Over.map (thick R I e)).obj T) hN hN' d hd β
  have h : ∀ x : T ⟶ thickObj R I e G, a x.left * W' x = W x * d (β x) := fun x => by
    rw [ha, hW, hW', hd]
    exact sq _ x.left z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)
  refine ⟨fun x => ?_, fun x y v => ?_⟩
  · exact even_alg (a := fun x => a x.left) (d := fun x => d (β x)) h (s₁ x) (s₂ x) (s₃ x)
  · obtain ⟨c, hc⟩ : ∃ c : (T.left.presheaf.stalk z)ˣ,
      c = cubV U.P.c (T := (Over.map (thick R I e)).obj T) z N (β x) (β y) (β v) := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c : (T.left.presheaf.stalk z)ˣ,
      c = cubV U'.P.c (T := (Over.map (thick R I e)).obj T) z N' (β x) (β y) (β v) := ⟨_, rfl⟩
    have k₁ : cubP (U.gt e) z J x y v * W (x * y) * W (x * v) * W (y * v) * W 1 =
      W (x * y * v) * W x * W y * W v * c := (c₁ x y v).trans (congrArg (_ * ·) hc.symm)
    have k₂ : cubP (U'.gt e) z J' x y v * W' (x * y) * W' (x * v) * W' (y * v) * W' 1 =
      W' (x * y * v) * W' x * W' y * W' v * c' := (c₂ x y v).trans (congrArg (_ * ·) hc'.symm)
    have k₃ : c * d (β (x * y)) * d (β (x * v)) * d (β (y * v)) * d (β 1) =
        d (β (x * y * v)) * d (β x) * d (β y) * d (β v) * c' := by
      rw [hc, hc']; exact c₃ x y v
    have k := cube_alg (A := T ⟶ thickObj R I e G) (a := fun x => a x.left) (d := fun x => d (β x)) h k₁ k₂ k₃
    exact k

end PreTorusInvariance


open TorusInvariance PreTorusInvariance in
set_option maxHeartbeats 400000 in
theorem preU_comparison_torus_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∀ (e : ℕ) (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A), (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' → gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') = gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.P.L.ι) (jM' : D'.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.P.L.U jM' → gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = gw u y.left z jM (fun _ => jM') := by
  intro R _ _ _ I D D' A A' G _ _ U U' wL hw hL e β hβ u hu sq Z₀ τ₀ y₀ z₀ jM jM' m m'
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U.gt e).i_hom
  have := U.semi.geomConnected
  have := connectedSpace_spec_quotient (I ^ (e + 1)) (Z₀.hom z₀)
  have : GeometricallyConnected (thickObj R I e G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
  have : ConnectedSpace (thickObj R I e G).left :=
    GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
  have hq : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X),
      (τ ≫ (U.gt e).i) ≫ (U.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U.gt e).q := fun τ => by
    rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have hq' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X),
      (τ ≫ (U.gt e).i) ≫ (U'.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U'.gt e).q := fun τ => by
    rw [← cancel_mono β.hom, Category.assoc _ _ β.hom, Category.assoc _ _ β.hom, hβ]
    exact hq τ
  have hp : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U.gt e).pG.left = y.left ≫ (U.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq, ← MonObj.mul_comp, _root_.one_mul])
  have hp' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U'.gt e).pG.left = y.left ≫ (U'.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq', ← MonObj.mul_comp, _root_.one_mul])
  obtain ⟨ρ, key⟩ := exists_ratio_translate (U.gt e).i D.P.isLB D'.P.isLB u hu (fun _ => hp) (fun _ => hp')
  have triv := ratio_eq_one (U.gt e).i ρ (fun Z z => by
    obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
    obtain ⟨J', hJ'⟩ := exists_good_pt D'.P.isLB z
    obtain ⟨a, ha⟩ : ∃ a : (Z.left ⟶ (thickObj R I e G).left) → (Z.left.presheaf.stalk z)ˣ,
      ∀ r, a r = gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := ⟨_, fun _ => rfl⟩
    obtain ⟨s, c⟩ := vals u hL sq hJ hJ' a ha
    refine ⟨a, fun t y => ?_, fun t t' y => ?_, fun t => ?_⟩
    · rw [ha, ha, hp, hp']
      exact key Z t y z _ _ (hJ _) (hJ' _)
    · have p := c (t ≫ (U.gt e).i) (t' ≫ (U.gt e).i) y
      have q := c 1 1 y
      rw [cubP_congr (U.gt e) z J y (hq t) (hq t'), cubP_congr (U'.gt e) z J' y (hq' t) (hq' t')] at p
      rw [prod_psum, prod_psum]
      exact mul_right_cancel (p.symm.trans q)
    · have p := s (t ≫ (U.gt e).i)
      have q := s 1
      rw [pG_congr (U.gt e) (hq t), pG_congr (U'.gt e) (hq' t)] at p
      exact cancel_even p q)
  rw [key Z₀ τ₀ y₀ z₀ jM jM' m m', triv, map_one, _root_.one_mul]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PsiRing

def FibNZ {Y S : Scheme.{0}} (p : Y ⟶ S) {M : LB Y} (s : LB.Sec M) : Prop :=
  ∀ y : S, ∃ z : Y, p z = y ∧ z ∈ nonzeroLocus s

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def Mult (D : DegPre R) (th g : SecBT D (𝟙_ _) 1 0) (b : R) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval g r z J = cst (r ≫ (𝟙_ _ ⊗ D.P.A).hom) z b * sval th r z J

def Coef (D : DegPre R) (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (th : SecBT D (𝟙_ _) 1 0) (g : SecBT D (𝟙_ _) 1 χ) (b : R) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    sval g (lift (toUnit T) y).left z J = cst T.hom z b * ((val u (toUnit T).left z J * rigV D z J).val *
      sval th (lift (toUnit T) (y * cT D T χ)).left z J)

def SecCmp (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β))
    (xe : D'.X ≃+ D.X) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α) : Prop :=
  ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
    r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' →
      sval (f (xe α)) r z J = (∏ i : Fin 4, gw v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ β))
        (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε 1 i).val * sval (f' α) r' z J'

abbrev RigCmp (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left)
    (v : LB.Iso D'.P.L (D.P.L.pull β)) : Prop :=
  PMaps v (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ)

abbrev PsiCmp (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β))
    (xe : D'.X ≃+ D.X) (gam : (TK V).left ⟶ (TK R).left) : Prop :=
  ∀ x, PMaps v (K := PUnit) (fun _ => D'.xK x) (fun _ => D.xK (xe x)) (fun _ => -1) (D'.psi x) (D.psi (xe x)) gam

end GlobalTheory.PsiRing
end
end

