module

public import Mathlib

@[expose] public section

noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

def vv (k : Type) [Field k] : k⸨X⸩ := HahnSeries.single 1 1

structure RingPG (k : Type) [Field k] (l : ℕ) where

  φ : k⸨X⸩ →ₐ[k] k⸨X⸩

  γ : k⸨X⸩ →ₐ[k] k⸨X⸩

  φ_int : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, φ (a : k⸨X⸩) = (b : k⸨X⸩)

  γ_int : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, γ (a : k⸨X⸩) = (b : k⸨X⸩)

  φ_v : ∃ u : (k⟦X⟧)ˣ, φ (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ l

  γ_v : ∃ κ : k⟦X⟧, PowerSeries.constantCoeff κ = 1 ∧ γ (vv k) = vv k * (1 - (κ : k⸨X⸩) * vv k)

  comm : ∀ x, φ (γ x) = γ (φ x)

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

def IsLat (N : Submodule k⟦X⟧ V) : Prop := N.FG ∧ Submodule.span k⸨X⸩ (N : Set V) = ⊤

def sh (a : ℤ) (N : Submodule k⟦X⟧ V) : Submodule k⟦X⟧ V :=
  N.map ((vv k ^ a • (LinearMap.id : V →ₗ[k⸨X⸩] V)).restrictScalars k⟦X⟧)

def Semi {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k W] (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (f : W →ₗ[k] V) : Prop :=
  ∀ (a : k⸨X⸩) (x : W), f (a • x) = σ a • f x

def nab (g : V →ₗ[k] V) : V →ₗ[k] V :=
  (((vv k)⁻¹ • (LinearMap.id : V →ₗ[k⸨X⸩] V)).restrictScalars k) ∘ₗ (g - LinearMap.id)

def pull (f : V →ₗ[k] V) (N : Submodule k⟦X⟧ V) : Submodule k⟦X⟧ V :=
  Submodule.span k⟦X⟧ (f '' (N : Set V))

def CondC (g : V →ₗ[k] V) (N : Submodule k⟦X⟧ V) : Prop := ∀ x ∈ N, g x - x ∈ sh 1 N

def gmult {U : Type} [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q : Submodule k U) (x : k) : ℕ :=
  Module.finrank k (↥(P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m)) ⧸
    Q.submoduleOf (P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m)))

def qmult (g : V →ₗ[k] V) (P Q : Submodule k⟦X⟧ V) (x : k) : ℕ :=
  gmult (nab g) (P.restrictScalars k) (Q.restrictScalars k) x

def sen (g : V →ₗ[k] V) (N : Submodule k⟦X⟧ V) (x : k) : ℕ := qmult g N (sh 1 N) x

structure ModPG {l : ℕ} (R : RingPG k l) (n : ℕ) (V : Type) [AddCommGroup V] [Module k⸨X⸩ V] [Module k V] where

  φ : ZMod n → V →ₗ[k] V

  γ : ZMod n → V →ₗ[k] V

  φ_semi : ∀ i, Semi R.φ (φ i)

  γ_semi : ∀ i, Semi R.γ (γ i)

  etale : ∀ i, Submodule.span k⸨X⸩ (Set.range (φ i)) = ⊤

  γ_bij : ∀ i, Function.Bijective (γ i)

  comm : ∀ i x, φ i (γ (i - 1) x) = γ i (φ i x)

  fin : Module.Finite k⸨X⸩ V := by infer_instance

  tower : IsScalarTower k k⸨X⸩ V := by infer_instance

def CondAB {n : ℕ} (φ : ZMod n → V →ₗ[k] V) (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V) : Prop :=
  ∀ i, pull (φ i) (N (i - 1)) ≤ sh (-w i) (N i) ∧ sh (w' i) (N i) ≤ pull (φ i) (N (i - 1))

def sg (l : ℕ) {n : ℕ} (h : ZMod n → ℕ) (i : ZMod n) : ℕ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊

end

section
variable (k : Type) [Field k]

theorem const_smul_eq (c : k) (x : k⸨X⸩) : c • x = algebraMap k k⸨X⸩ c * x := by
  have h : algebraMap k k⸨X⸩ c = HahnSeries.C c := by
    change HahnSeries.ofPowerSeries ℤ k (PowerSeries.C c) = _
    simp
  rw [h, HahnSeries.C_mul_eq_smul]

instance towerLaurent : IsScalarTower k k⸨X⸩ k⸨X⸩ := ⟨fun a b c => by
  rw [const_smul_eq, const_smul_eq, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

instance towerPower : IsScalarTower k k⟦X⟧ k⸨X⸩ := ⟨fun a b c => by
  rw [const_smul_eq, Algebra.smul_def a b, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]; rfl⟩

theorem vv_eq_coe_X : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by simp [vv]

theorem vv_ne_zero : vv k ≠ 0 := by simp [vv]

end

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]

section
variable [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem mem_sh_iff_exists {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ ∃ y ∈ N, vv k ^ a • y = x := Iff.rfl

theorem mem_sh_iff_smul_mem {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ vv k ^ (-a) • x ∈ N := by
  have hv := vv_ne_zero k
  constructor
  · rintro ⟨y, hy, rfl⟩
    change vv k ^ (-a) • vv k ^ a • y ∈ N
    rwa [smul_smul, ← zpow_add₀ hv, neg_add_cancel, zpow_zero, one_smul]
  · intro h
    refine mem_sh_iff_exists.2 ⟨_, h, ?_⟩
    rw [smul_smul, ← zpow_add₀ hv, add_neg_cancel, zpow_zero, one_smul]

theorem sh_zero_eq (N : Submodule k⟦X⟧ V) : sh 0 N = N := by
  ext x; simp [mem_sh_iff_smul_mem]

theorem sh_sh_eq (a b : ℤ) (N : Submodule k⟦X⟧ V) : sh a (sh b N) = sh (a + b) N := by
  ext x
  simp only [mem_sh_iff_smul_mem, smul_smul, ← zpow_add₀ (vv_ne_zero k), neg_add_rev]

theorem sh_le_sh (a : ℤ) {N N' : Submodule k⟦X⟧ V} (h : N ≤ N') : sh a N ≤ sh a N' :=
  Submodule.map_mono h

theorem sh_le_sh_of_le {a b : ℤ} (h : b ≤ a) (N : Submodule k⟦X⟧ V) : sh a N ≤ sh b N := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨m, rfl⟩ := Int.le.dest h
  refine mem_sh_iff_exists.2 ⟨(PowerSeries.X ^ m : k⟦X⟧) • y, N.smul_mem _ hy, ?_⟩
  change _ = vv k ^ (b + m) • y
  rw [← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ m : k⟦X⟧) y, smul_smul, zpow_add₀ (vv_ne_zero k), zpow_natCast,
    map_pow]
  congr 3
  exact (vv_eq_coe_X k).symm

theorem IsLat.shift {N : Submodule k⟦X⟧ V} (h : IsLat N) (a : ℤ) : IsLat (sh a N) := by
  refine ⟨h.1.map _, eq_top_iff.2 ?_⟩
  rw [← h.2]
  refine Submodule.span_le.2 fun y hy => ?_
  have h1 : vv k ^ a • y ∈ Submodule.span k⸨X⸩ (sh a N : Set V) :=
    Submodule.subset_span (mem_sh_iff_exists.2 ⟨y, hy, rfl⟩)
  exact (Submodule.smul_mem_iff _ (zpow_ne_zero a (vv_ne_zero k))).1 h1


omit [IsScalarTower k⟦X⟧ k⸨X⸩ V] in
theorem pull_le_pull [Module k V] (f : V →ₗ[k] V) {N N' : Submodule k⟦X⟧ V} (h : N ≤ N') :
    pull f N ≤ pull f N' :=
  Submodule.span_mono (Set.image_mono h)

end

theorem nab_apply_eq [Module k V] [IsScalarTower k k⸨X⸩ V] (g : V →ₗ[k] V) (x : V) :
    nab g x = (vv k)⁻¹ • (g x - x) := rfl

theorem condC_iff_nab_mem [Module k V] [IsScalarTower k k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
    (g : V →ₗ[k] V) (N : Submodule k⟦X⟧ V) : CondC g N ↔ ∀ x ∈ N, nab g x ∈ N := by
  simp only [CondC, mem_sh_iff_smul_mem, nab_apply_eq, zpow_neg_one]

variable [Module k V] {l n : ℕ} {R : RingPG k l}

theorem ModPG.span_φ (D : ModPG R n V) (i : ZMod n) {ι : Type} (b : Module.Basis ι k⸨X⸩ V) :
    Submodule.span k⸨X⸩ (Set.range fun j => D.φ i (b j)) = ⊤ := by
  rw [eq_top_iff, ← D.etale i]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Submodule.span k⸨X⸩ (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [D.φ_semi i a y]; exact Submodule.smul_mem _ _ hy

theorem ModPG.linearIndependent_φ (D : ModPG R n V) (i : ZMod n) {ι : Type} (b : Module.Basis ι k⸨X⸩ V) :
    LinearIndependent k⸨X⸩ fun j => D.φ i (b j) := by
  haveI := D.fin
  haveI := FiniteDimensional.fintypeBasisIndex b
  exact linearIndependent_of_top_le_span_of_card_eq_finrank (D.span_φ i b).ge
    (Module.finrank_eq_card_basis b).symm

end

theorem summable_sg {l n : ℕ} [NeZero n] (hl : 2 ≤ l) (h : ZMod n → ℕ) (i : ZMod n) :
    Summable fun j : ℕ => (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hg : Summable fun j : ℕ => ((∑ t, h t : ℕ) : ℝ) * ((l : ℝ)⁻¹) ^ (j + 1) :=
    ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by linarith)))).mul_left _
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hg
  rw [div_eq_mul_inv, inv_pow]
  gcongr
  exact Finset.single_le_sum (f := h) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)

namespace Inh
variable {k : Type} [Field k]

def extend (f : k⟦X⟧ →ₐ[k] k⟦X⟧) (hf : f PowerSeries.X ≠ 0) : k⸨X⸩ →ₐ[k] k⸨X⸩ :=
  { IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : k⟦X⟧)) (S := k⸨X⸩)
      (g := (algebraMap k⟦X⟧ k⸨X⸩).comp f.toRingHom) (by
        rintro ⟨y, m, rfl⟩
        refine isUnit_iff_ne_zero.2 ?_
        simp only [RingHom.comp_apply, map_pow]
        exact pow_ne_zero _ fun h' =>
          hf (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using h'))) with
    commutes' := fun c => by
      have h : algebraMap k k⸨X⸩ c = algebraMap k⟦X⟧ k⸨X⸩ (algebraMap k k⟦X⟧ c) := rfl
      simp only [h]
      change IsLocalization.lift _ _ = _
      rw [IsLocalization.lift_eq]
      exact congrArg (algebraMap k⟦X⟧ k⸨X⸩) (f.commutes c) }

theorem extend_coe (f : k⟦X⟧ →ₐ[k] k⟦X⟧) (hf : f PowerSeries.X ≠ 0) (a : k⟦X⟧) :
    extend f hf (a : k⸨X⸩) = ((f a : k⟦X⟧) : k⸨X⸩) :=
  IsLocalization.lift_eq (M := Submonoid.powers (PowerSeries.X : k⟦X⟧)) (S := k⸨X⸩) _ a

theorem algHom_ext {f g : k⸨X⸩ →ₐ[k] k⸨X⸩} (h : ∀ a : k⟦X⟧, f (a : k⸨X⸩) = g (a : k⸨X⸩)) (x : k⸨X⸩) :
    f x = g x := by
  have : f.toRingHom = g.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : k⟦X⟧))
    exact RingHom.ext h
  exact RingHom.congr_fun this x

def inv1 (c : k) : k⟦X⟧ := PowerSeries.invOfUnit (1 + PowerSeries.C c * PowerSeries.X) 1

theorem powerSeries_oneAddConstMulX_mul_inv (c : k) : (1 + PowerSeries.C c * PowerSeries.X) * inv1 c = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)

theorem hasSubst_mob (c : k) : PowerSeries.HasSubst (PowerSeries.X * inv1 c : k⟦X⟧) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

def mob (c : k) : k⟦X⟧ →ₐ[k] k⟦X⟧ := PowerSeries.substAlgHom (hasSubst_mob c)

theorem mob_X (c : k) : mob c PowerSeries.X = PowerSeries.X * inv1 c := PowerSeries.substAlgHom_X _

theorem mob_C (c d : k) : mob c (PowerSeries.C d) = PowerSeries.C d := (mob c).commutes d

theorem mob_X_ne (c : k) : mob c PowerSeries.X ≠ 0 := by
  rw [mob_X]
  exact mul_ne_zero PowerSeries.X_ne_zero (right_ne_zero_of_mul_eq_one (powerSeries_oneAddConstMulX_mul_inv c))

theorem mob_mob (c : k) (f : k⟦X⟧) : mob c (mob (-c) f) = f := by
  have key : mob c (PowerSeries.X * inv1 (-c)) = PowerSeries.X := by
    have h1 := congrArg (mob c) (powerSeries_oneAddConstMulX_mul_inv (-c))
    rw [map_mul, map_add (f := _), map_one, map_mul, mob_C, mob_X, map_neg] at h1
    have h2 := powerSeries_oneAddConstMulX_mul_inv c
    rw [map_mul, mob_X]
    linear_combination PowerSeries.X * h1 + PowerSeries.X * mob c (inv1 (-c)) * h2
  have h := PowerSeries.subst_comp_subst_apply (R := k) (hasSubst_mob (-c)) (hasSubst_mob c) f
  rw [mob, PowerSeries.coe_substAlgHom] at key
  rw [key, PowerSeries.X_subst] at h
  simpa only [mob, PowerSeries.coe_substAlgHom] using h

def gam (k : Type) [Field k] : k⸨X⸩ →ₐ[k] k⸨X⸩ := extend (mob 1) (mob_X_ne 1)

theorem extend_mob_mob (c : k) (x : k⸨X⸩) :
    extend (mob c) (mob_X_ne c) (extend (mob (-c)) (mob_X_ne (-c)) x) = x :=
  algHom_ext (f := (extend (mob c) (mob_X_ne c)).comp (extend (mob (-c)) (mob_X_ne (-c)))) (g := AlgHom.id _ _)
    (fun a => by simp only [AlgHom.comp_apply, extend_coe, mob_mob, AlgHom.id_apply]) x

theorem gam_bijective : Function.Bijective (gam k) :=
  ⟨RingHom.injective (gam k).toRingHom, fun x => ⟨_, extend_mob_mob 1 x⟩⟩

theorem hasSubst_pow (l : ℕ) [Fact l.Prime] : PowerSeries.HasSubst (PowerSeries.X ^ l : k⟦X⟧) :=
  PowerSeries.HasSubst.X_pow (Fact.out : l.Prime).ne_zero

def frob (k : Type) [Field k] (l : ℕ) [Fact l.Prime] : k⟦X⟧ →ₐ[k] k⟦X⟧ :=
  PowerSeries.substAlgHom (hasSubst_pow l)

theorem frob_X (l : ℕ) [Fact l.Prime] : frob k l PowerSeries.X = PowerSeries.X ^ l :=
  PowerSeries.substAlgHom_X _

theorem frob_X_ne (l : ℕ) [Fact l.Prime] : frob k l PowerSeries.X ≠ 0 := by
  rw [frob_X]; exact pow_ne_zero _ PowerSeries.X_ne_zero

theorem frob_mob (l : ℕ) [Fact l.Prime] [CharP k l] (f : k⟦X⟧) :
    frob k l (mob 1 f) = mob 1 (frob k l f) := by
  haveI : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l
  have key : frob k l (PowerSeries.X * inv1 1) = mob 1 (PowerSeries.X ^ l) := by
    have h0 := powerSeries_oneAddConstMulX_mul_inv (1 : k)
    rw [map_one, one_mul] at h0
    have h1 := congrArg (frob k l) h0
    rw [map_mul, map_add (f := _), map_one, frob_X] at h1
    have h2 := congrArg (· ^ l) h0
    simp only [mul_pow, add_pow_char, one_pow] at h2
    rw [map_mul, frob_X, map_pow, mob_X, mul_pow]
    congr 1
    linear_combination (inv1 (1 : k)) ^ l * h1 - frob k l (inv1 1) * h2
  have h := PowerSeries.subst_comp_subst_apply (R := k) (hasSubst_mob (1 : k)) (hasSubst_pow (k := k) l) f
  have h' := PowerSeries.subst_comp_subst_apply (R := k) (hasSubst_pow (k := k) l) (hasSubst_mob (1 : k)) f
  simp only [frob, mob, PowerSeries.coe_substAlgHom] at key ⊢
  rw [h, h', key]

def stdRing (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] : RingPG k l where
  φ := extend (frob k l) (frob_X_ne l)
  γ := gam k
  φ_int a := ⟨_, extend_coe _ _ a⟩
  γ_int a := ⟨_, extend_coe _ _ a⟩
  φ_v := ⟨1, by rw [vv_eq_coe_X, extend_coe, frob_X]; simp⟩
  γ_v := ⟨inv1 1, by simp [inv1], by
    rw [gam, vv_eq_coe_X, extend_coe, mob_X, ← map_mul, ← map_one (HahnSeries.ofPowerSeries ℤ k), ← map_sub,
      ← map_mul]
    congr 1
    have := powerSeries_oneAddConstMulX_mul_inv (1 : k)
    rw [map_one] at this
    linear_combination PowerSeries.X * this⟩
  comm x := by
    refine algHom_ext (f := (extend (frob k l) (frob_X_ne l)).comp (gam k))
      (g := (gam k).comp (extend (frob k l) (frob_X_ne l))) (fun a => ?_) x
    simp only [AlgHom.comp_apply, gam, extend_coe, frob_mob]

def lin (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) : k⸨X⸩ →ₗ[k] k⸨X⸩ where
  toFun := σ
  map_add' := map_add σ
  map_smul' c x := by simp only [const_smul_eq, map_mul, AlgHom.commutes, RingHom.id_apply]

@[simp] theorem lin_apply (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (x : k⸨X⸩) : lin σ x = σ x := rfl

def powMod {l : ℕ} (R : RingPG k l) (hγ : Function.Bijective R.γ) (n r : ℕ) : ModPG R n (Fin r → k⸨X⸩) where
  φ _ := (lin R.φ).compLeft (Fin r)
  γ _ := (lin R.γ).compLeft (Fin r)
  φ_semi _ a x := funext fun j => map_mul R.φ a (x j)
  γ_semi _ a x := funext fun j => map_mul R.γ a (x j)
  etale _ := by
    rw [eq_top_iff, ← (Pi.basisFun k⸨X⸩ (Fin r)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.basisFun k⸨X⸩ (Fin r) j, funext fun t => ?_⟩
    simp [Pi.single_apply, apply_ite R.φ]
  γ_bij _ := hγ.comp_left
  comm _ x := funext fun j => R.comm (x j)

def stdLat (k : Type) [Field k] : Submodule k⟦X⟧ k⸨X⸩ := Submodule.span k⟦X⟧ {1}

theorem mem_stdLat {x : k⸨X⸩} : x ∈ stdLat k ↔ ∃ a : k⟦X⟧, (a : k⸨X⸩) = x := by
  simp [stdLat, Submodule.mem_span_singleton, Algebra.smul_def]

theorem isLat_stdLat : IsLat (stdLat k) := by
  refine ⟨Submodule.fg_span_singleton _, eq_top_iff.2 fun x _ => ?_⟩
  have h1 : (1 : k⸨X⸩) ∈ Submodule.span k⸨X⸩ (stdLat k : Set k⸨X⸩) :=
    Submodule.subset_span (Submodule.mem_span_singleton_self _)
  simpa using Submodule.smul_mem _ x h1

end Inh

end GlobalTheory.PhiGam
