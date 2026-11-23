module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalBoundOfPeriodClassStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_bound_of_period_class : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F), K.Rich → ∀ (r : Real K s σ) (f : Form s) (per : Λ →+ Hol F.V), r.coef.pull1 (Form.cl s f) = K.perCl per → ∃ (q : GlobalTheory.CatCoh.C0 K.Oc) (G : Tot I g → ℂ), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 ∧ AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, Hol.fn (W := K.W k) (q (K.triv k)) p = G p) ∧ ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → G (F.shift l p) = G p + (per l).fn p.1 := by
  first | exact @GlobalTheory.AnPer.Charts.exists_bound_glue | exact GlobalTheory.AnPer.Charts.exists_bound_glue | (intros; apply GlobalTheory.AnPer.Charts.exists_bound_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveKernelCoindIntertwiningMap
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.CoindKernel

variable {G : Type} [Group G] (P : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ P V)


open Classical in
noncomputable def delta : V →ₗ[ℂ] Representation.coindV P.subtype σ where
  toFun v := ⟨fun x => if h : x ∈ P then σ ⟨x, h⟩ v else 0, by
    intro p g
    by_cases hg : g ∈ P
    · have h1 : P.subtype p * g ∈ P := P.mul_mem p.2 hg
      simp only [dif_pos hg, dif_pos h1]
      have : (⟨P.subtype p * g, h1⟩ : P) = p * ⟨g, hg⟩ := rfl
      rw [this, map_mul]; rfl
    · have h1 : P.subtype p * g ∉ P := fun h => hg ((P.mul_mem_cancel_left p.2).1 h)
      simp only [dif_neg hg, dif_neg h1, map_zero]⟩
  map_add' v w := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]
  map_smul' c v := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]

open Classical in
theorem delta_apply (v : V) (x : G) :
    (delta P σ v).1 x = if h : x ∈ P then σ ⟨x, h⟩ v else 0 := rfl

theorem coind_val (g : G) (f : Representation.coindV P.subtype σ) (x : G) :
    (Representation.coind P.subtype σ g f).1 x = f.1 (x * g) := rfl

theorem coind_delta (p : P) (v : V) :
    Representation.coind P.subtype σ (p : G) (delta P σ v) = delta P σ (σ p v) := by
  ext x
  rw [coind_val, delta_apply, delta_apply]
  by_cases hx : x ∈ P
  · have h1 : x * (p : G) ∈ P := P.mul_mem hx p.2
    rw [dif_pos hx, dif_pos h1]
    have : (⟨x * (p : G), h1⟩ : P) = ⟨x, hx⟩ * p := rfl
    rw [this, map_mul]; rfl
  · have h1 : x * (p : G) ∉ P := fun h => hx ((P.mul_mem_cancel_right p.2).1 h)
    rw [dif_neg hx, dif_neg h1]

open Classical in
theorem sum_delta [Fintype G] (f : Representation.coindV P.subtype σ) :
    ∑ g : G, Representation.coind P.subtype σ g⁻¹ (delta P σ (f.1 g)) =
      ((Finset.univ.filter (· ∈ P)).card : ℂ) • f := by
  ext x
  have h : ∀ g : G, (Representation.coind P.subtype σ g⁻¹ (delta P σ (f.1 g))).1 x
      = if x * g⁻¹ ∈ P then f.1 x else 0 := by
    intro g
    rw [coind_val, delta_apply]
    by_cases hx : x * g⁻¹ ∈ P
    · rw [dif_pos hx, if_pos hx]
      have := f.2 ⟨x * g⁻¹, hx⟩ g
      rw [← this]
      simp
    · rw [dif_neg hx, if_neg hx]
  rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_congr rfl fun g _ => h g]
  have e := Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft x))
    (fun y : G => if y ∈ P then f.1 x else 0)
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at e
  rw [e, ← Finset.sum_filter, Finset.sum_const, Submodule.coe_smul, Pi.smul_apply,
    Nat.cast_smul_eq_nsmul]

variable (P' : Subgroup G) {V' : Type} [AddCommGroup V'] [Module ℂ V']
  (σ' : Representation ℂ P' V')

noncomputable def kernel :
    Representation.IntertwiningMap (Representation.coind P.subtype σ)
      (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V') where
  toFun Φ g := (LinearMap.proj g ∘ₗ (Representation.coindV P'.subtype σ').subtype) ∘ₗ
    Φ.toLinearMap ∘ₗ delta P σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernel_apply (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ)
      (Representation.coind P'.subtype σ')) (g : G) (v : V) :
    kernel P σ P' σ' Φ g v = (Φ (delta P σ v)).1 g := rfl

theorem exists_kernel : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V'), ∃ K : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V'), Function.Injective K ∧ ∀ (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ')) (p' : P') (g : G) (p : P), K Φ ((p' : G) * g * (p : G)) = σ' p' ∘ₗ K Φ g ∘ₗ σ p := by
  intro G _ _ P P' V V' _ _ _ _ σ σ'
  classical
  haveI := Fintype.ofFinite G
  refine ⟨kernel P σ P' σ', ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro Φ hΦ
    have h0 : ∀ v, Φ (delta P σ v) = 0 := by
      intro v
      ext g
      have := kernel_apply P σ P' σ' Φ g v
      rw [hΦ] at this
      exact this.symm
    apply Representation.IntertwiningMap.ext
    ext1 f
    have h1 := congrArg Φ (sum_delta P σ f)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul, Finset.sum_eq_zero (fun g _ => by
      rw [Φ.isIntertwining, h0, map_zero])] at h1
    have hc : ((Finset.univ.filter (fun x : G => x ∈ P)).card : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero, Finset.card_ne_zero]
      exact ⟨1, by simp [P.one_mem]⟩
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  · intro Φ p' g p
    ext v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, kernel_apply, kernel_apply, ← coind_delta,
      Φ.isIntertwining, coind_val, mul_assoc]
    exact (Φ (delta P σ v)).2 p' (g * p)

end GlobalTheory.CoindKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConnIsEtSplitting
section
set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem exists_isConn_isEt_splitting :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      ∃ (G₀ G₁ : PDivGroup p k) (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (i₁ : G₁ ⟶ G) (q₁ : G ⟶ G₁),
        G₀.IsConn ∧ G₁.IsEt ∧ i₀ ≫ q₀ = 𝟙 G₀ ∧ i₁ ≫ q₁ = 𝟙 G₁ ∧ q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G := by
  intro p _ k _ _ _ G
  obtain ⟨e, he, hnil, hred⟩ := _root_.GlobalTheory.PDivGroup.exists_perfect_idempotent p k G
  have h1 : e + (𝟙 G - e) = 𝟙 G := add_sub_cancel _ _
  have h1' : (𝟙 G - e) + e = 𝟙 G := sub_add_cancel _ _
  have h2 : e ≫ (𝟙 G - e) = 0 := by rw [Preadditive.comp_sub, Category.comp_id, he, sub_self]
  have h3 : (𝟙 G - e) ≫ e = 0 := by rw [Preadditive.sub_comp, Category.id_comp, he, sub_self]
  obtain ⟨G₀, i₀, q₀, a₀, b₀, c₀⟩ := GlobalTheory.T.pDivGroup_idempotent_split_field p k G e (𝟙 G - e) h1 h2 h3
  obtain ⟨G₁, i₁, q₁, a₁, b₁, c₁⟩ := GlobalTheory.T.pDivGroup_idempotent_split_field p k G (𝟙 G - e) e h1' h3 h2
  refine ⟨G₀, G₁, i₀, q₀, i₁, q₁, fun n x hx => ?_, fun n => ⟨fun x hx => ?_⟩, a₀, a₁,
    by rw [b₀, b₁, h1']⟩
  · obtain ⟨a, rfl⟩ := (c₀ n).1 x
    have ha : a ∈ augIdeal k (G.A n) := by
      have hx' : counit (R := k) (i₀.app n a) = 0 := hx
      rw [CoalgHomClass.counit_comp_apply] at hx'
      exact hx'
    have hk : e.app n a ∈ RingHom.ker (i₀.app n) := by
      rw [(c₀ n).2]
      exact Ideal.mem_map_of_mem (e.app n : G.A n →ₐ[k] G.A n) ha
    have := (hnil n a).map (i₀.app n)
    rwa [map_sub, RingHom.mem_ker.1 hk, sub_zero] at this
  · obtain ⟨a, rfl⟩ := (c₁ n).1 x
    have hq : q₁.app n (i₁.app n a) = e.app n a := congrArg (fun g : G ⟶ G => g.app n a) b₁
    have hi : i₁.app n (q₁.app n (i₁.app n a)) = i₁.app n a :=
      congrArg (fun g : G₁ ⟶ G₁ => g.app n (i₁.app n a)) a₁
    have h0 : e.app n a = 0 := hred n a (hq ▸ hx.map (q₁.app n))
    rw [← hi, hq, h0, map_zero]

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebra
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPFlat

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R} (κ : DividedPowers I)

def expS (z : R) (y : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ y ^ n * algebraMap R A (κ.dpow n z)

theorem expS_add_right {z : R} (hz : z ∈ I) (y y' : A) :
    expS κ z (y + y') = expS κ z y * expS κ z y' := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) *
      (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) =
      y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := κ.mul_dpow (m := p.1) (n := p.2) hz
    rw [hp] at h
    calc _ = y ^ p.1 * y' ^ p.2 * algebraMap R A (κ.dpow p.1 z * κ.dpow p.2 z) := by
            rw [map_mul]; ring
      _ = _ := by rw [h, map_mul, map_natCast]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem expS_add_left {z z' : R} (hz : z ∈ I) (hz' : z' ∈ I) (y : A) :
    expS κ (z + z') y = expS κ z y * expS κ z' y := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]; ring

theorem expS_smul {z : R} (hz : z ∈ I) (a : R) (y : A) :
    expS κ z (algebraMap R A a * y) = expS κ (a * z) y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]
  ring

theorem expS_zero_left (y : A) : expS κ 0 y = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero hn, hn]

theorem expS_zero_right (z : R) (hz : z ∈ I) : expS κ z (0 : A) = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero hz]
  · simp [hn]

theorem expS_sum_right {z : R} (hz : z ∈ I) {K : Type} (s : Finset K) (f : K → A) :
    expS κ z (∑ k ∈ s, f k) = ∏ k ∈ s, expS κ z (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_right κ z hz]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]

theorem expS_sum_left {K : Type} (s : Finset K) (f : K → R) (hf : ∀ k ∈ s, f k ∈ I) (y : A) :
    expS κ (∑ k ∈ s, f k) y = ∏ k ∈ s, expS κ (f k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_left κ y]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk,
      expS_add_left κ (hf k (Finset.mem_insert_self k s))
        (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

theorem prod_expS_eq_one [Module.Flat R A] (c : I →₀ A)
    (hc : (c.sum fun i a ↦ a * algebraMap R A i) = 0) :
    (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * algebraMap R A (κ.dpow n i)) = 1 := by
  have h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A) := by
    rw [Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h
  simp only at hx ha
  change (∏ i ∈ c.support, expS κ (i : R) (c i)) = 1
  rw [← Finset.prod_coe_sort]
  calc ∏ i : c.support, expS κ ((i.1 : I) : R) (c i.1)
      = ∏ i : c.support, ∏ j, expS κ (a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [hx i, expS_sum_right κ (i.1 : I).2]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Algebra.smul_def, expS_smul κ (i.1 : I).2]
    _ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm
    _ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]
    _ = 1 := by
        refine Finset.prod_eq_one fun j _ ↦ ?_
        have : ∑ i : c.support, a i j * ((i.1 : I) : R) = 0 := by
          rw [← ha j]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
        rw [this, expS_zero_left]

theorem exists_isDPMorphism_of_flat : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I),
    ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  intro R A _ _ _ _ I κ
  let x : I → A := fun i ↦ algebraMap R A i
  have hspan : Ideal.span (Set.range x) = I.map (algebraMap R A) := by
    rw [Ideal.map]; congr 1; ext b; simp [x]
  obtain ⟨γ, hγ, hγx⟩ := _root_.GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ A I x (fun i n ↦ algebraMap R A (κ.dpow n i))
    (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2])
    (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n ↦ by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (prod_expS_eq_one κ)
  rw [hspan] at hγ
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens A _ γ (Set.range x) hγ hspan.symm (by
    rintro _ ⟨i, rfl⟩ m n hn
    rw [hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]
    simp only [κ.dpow_comp hn i.2, map_mul, map_natCast]
    rw [← hγx])
  exact ⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩

end GlobalTheory.DPFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviGeneratedCommutingBlockGL
section
noncomputable section

namespace GlobalTheory.Parabolic.LeviGen

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism Matrix

variable {F : Type} [Field F] {r d d' : ℕ}

theorem mem_range_blockEnum (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (i : Fin r) :
    i ∈ Set.range (blockEnum b c h) ↔ b i = c := by
  have e : Set.range (blockEnum b c h) = (block b c : Set (Fin r)) := Finset.range_orderEmbOfFin _ h
  rw [e]
  simp [block]

theorem extendMat_comm (e : Fin d ↪ Fin r) (e' : Fin d' ↪ Fin r) (h : ∀ a a', e a ≠ e' a')
    (M : Matrix (Fin d) (Fin d) F) (N : Matrix (Fin d') (Fin d') F) :
    extendMat e M * extendMat e' N = extendMat e' N * extendMat e M := by
  have h1 : (incl F e)ᵀ * incl F e' = 0 := by
    ext a a'
    simp [incl, Matrix.mul_apply, Matrix.one_apply, h a a']
  have h2 : (incl F e')ᵀ * incl F e = 0 := by
    ext a a'
    simp [incl, Matrix.mul_apply, Matrix.one_apply, (h a' a).symm]
  have h3 : incl F e * (M - 1) * (incl F e)ᵀ * (incl F e' * (N - 1) * (incl F e')ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl F e)ᵀ, h1]; simp
  have h4 : incl F e' * (N - 1) * (incl F e')ᵀ * (incl F e * (M - 1) * (incl F e)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl F e')ᵀ, h2]; simp
  simp only [extendMat, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [add_mul, mul_add, h3, h4, one_mul, mul_one]
  abel

def leviIncl (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    GL (Fin d) F →* levi F b :=
  ((blockTri (κ := F) b).subtype.comp (blockHom F b c h)).codRestrict _ fun g => by
    refine mem_levi.2 fun i j hij => ?_
    show extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) i j = 0
    rw [extendMat_out, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
    simp only [mem_range_blockEnum]
    omega

theorem leviIncl_val (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (g : GL (Fin d) F) :
    ((leviIncl F b c h g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) := rfl

def leviRes (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    levi F b →* GL (Fin d) F :=
  leviBlock b (blockEnum b c h) (blockEnum b c h).injective fun i j hij => by
    rw [mem_range_blockEnum, ← hij, blockEnum_mem b c h]

theorem leviRes_apply (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (m : levi F b) (a a' : Fin d) :
    (leviRes F b c h m : Matrix (Fin d) (Fin d) F) a a' =
      ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (blockEnum b c h a) (blockEnum b c h a') := rfl

theorem leviRes_leviIncl (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (g : GL (Fin d) F) :
    leviRes F b c h (leviIncl F b c h g) = g := by
  refine Units.ext (Matrix.ext fun a a' => ?_)
  rw [leviRes_apply, leviIncl_val, extendMat_in]

theorem leviRes_leviIncl_ne (b : Fin r → ℕ) {c c' : ℕ} (h : (block b c).card = d) (h' : (block b c').card = d')
    (hc : c' ≠ c) (g : GL (Fin d) F) : leviRes F b c' h' (leviIncl F b c h g) = 1 := by
  refine Units.ext (Matrix.ext fun a a' => ?_)
  rw [leviRes_apply, leviIncl_val, extendMat_out]
  · simp [Matrix.one_apply]
  · left
    rw [mem_range_blockEnum, blockEnum_mem b c' h']
    exact hc

theorem leviIncl_comm (b : Fin r → ℕ) {c c' : ℕ} (h : (block b c).card = d) (h' : (block b c').card = d')
    (hc : c ≠ c') (g : GL (Fin d) F) (g' : GL (Fin d') F) :
    Commute (leviIncl F b c h g) (leviIncl F b c' h' g') := by
  refine Subtype.ext (Units.ext ?_)
  refine extendMat_comm _ _ (fun a a' e => hc ?_) _ _
  rw [← blockEnum_mem b c h a, e, blockEnum_mem b c' h']

theorem iSup_range_leviIncl (b : Fin r → ℕ) (d : Set.range b → ℕ)
    (h : ∀ c : Set.range b, (block b c).card = d c) :
    (⨆ c : Set.range b, (leviIncl F b c (h c)).range) = ⊤ := by
  classical
  have key : ∀ s : Finset (Set.range b), ∀ m : levi F b,
      (∀ c : Set.range b, c ∉ s → leviRes F b c (h c) m = 1) →
        m ∈ ⨆ c : Set.range b, (leviIncl F b c (h c)).range := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro m hm
      have : m = 1 := by
        refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
        by_cases hij : b i = b j
        · let c : Set.range b := ⟨b i, i, rfl⟩
          obtain ⟨a, ha⟩ := (mem_range_blockEnum b c (h c) i).2 rfl
          obtain ⟨a', ha'⟩ := (mem_range_blockEnum b c (h c) j).2 hij.symm
          have h1 := leviRes_apply b c (h c) m a a'
          rw [hm c (Finset.notMem_empty _), ha, ha'] at h1
          rw [← h1]
          have : i = j ↔ a = a' := by rw [← (blockEnum b c (h c)).injective.eq_iff, ha, ha']
          simp [Matrix.one_apply, this]
        · rw [m.2 i j hij]
          simp [Matrix.one_apply_ne (fun e => hij (congrArg b e))]
      rw [this]
      exact Subgroup.one_mem _
    | insert c s _ ih =>
      intro m hm
      have e : m = m * leviIncl F b c (h c) (leviRes F b c (h c) m)⁻¹ *
          leviIncl F b c (h c) (leviRes F b c (h c) m) := by simp
      rw [e]
      refine Subgroup.mul_mem _ (ih _ fun c' hc' => ?_) (Subgroup.mem_iSup_of_mem c ⟨_, rfl⟩)
      by_cases hcc : c' = c
      · subst hcc
        rw [map_mul, leviRes_leviIncl, mul_inv_cancel]
      · rw [map_mul, leviRes_leviIncl_ne b _ _ (fun e => hcc (Subtype.ext e)), mul_one]
        exact hm c' (by simp [hcc, hc'])
  have := Fintype.ofFinite (Set.range b)
  exact eq_top_iff.2 fun m _ => key Finset.univ m fun c hc => absurd (Finset.mem_univ c) hc

theorem levi_generated : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ) (d : Set.range b → ℕ)
    (h : ∀ c : Set.range b, (block b c).card = d c), ∃ f : ∀ c : Set.range b, GL (Fin (d c)) F →* levi F b,
    (∀ (c : Set.range b) (g : GL (Fin (d c)) F),
      (f c g : GL (Fin r) F) = (blockHom F b c (h c) g : GL (Fin r) F)) ∧ (⨆ c, (f c).range) = ⊤ ∧
    ∀ c c' : Set.range b, c ≠ c' → ∀ (x : GL (Fin (d c)) F) (y : GL (Fin (d c')) F), Commute (f c x) (f c' y) :=
  fun F _ _ b d h => ⟨fun c => leviIncl F b c (h c), fun _ _ => rfl, iSup_range_leviIncl b d h,
    fun c c' hc x y => leviIncl_comm b (h c) (h c') (fun e => hc (Subtype.ext e)) x y⟩

end GlobalTheory.Parabolic.LeviGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosureThetaRatiosOfIsClStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_closure_theta_ratios_of_isCl' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (J : Type) (t : J → Ω), M.IsCl t → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  first | exact @GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl | exact GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl | (intros; apply GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hInv_of_directed_union_subalgebras : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (S : ι → Subalgebra ℤ A), Monotone S → (∀ a, ∃ i, a ∈ S i) → (∀ i, IsUnit (q : S i)) → (∀ i, HInv q (S i)) → HInv q A := by
  first | (exact @GlobalTheory.EtC.hInv_of_directed_union) | (exact GlobalTheory.EtC.hInv_of_directed_union) | (intros; apply GlobalTheory.EtC.hInv_of_directed_union  <;> assumption)
end

