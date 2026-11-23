module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology Classical

variable {K : UQ} (B : InvAlg K) {ι : Type}

abbrev al (K : UQ) (a : K.O) : K.E := algebraMap K.O K.E a

def InDual (s : B.A) (M : Submodule K.O B.A) : Prop :=
  ∀ z ∈ M, Algebra.trace K.E B.A (s * z) ∈ (algebraMap K.O K.E).range

def indM (M : Submodule K.O B.A) (y : B.A) : ℚ := if y ∈ M then 1 else 0

def indD (M : Submodule K.O B.A) (s : B.A) : ℚ := if InDual B s M then 1 else 0

def dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) : ℚ :=
  ∑ J ∈ I.powerset, (-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)

def term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) : ℚ :=
  dlt π I (indM B M) u * dlt π I' (indD B M) s

def HH (π : ι → B.A) (I I' : Finset ι) (u s : B.A) : ℚ :=
  ∑ᶠ M ∈ B.Lin, B.sgnLat M * term B π I I' u s M

def eS (e : ι → B.A) (I : Finset ι) : B.A := ∑ i ∈ I, e i

def Pos (a : K.O) (e : ι → B.A) (N : ℕ) (M : Submodule K.O B.A) (p : ι → ℤ) : Prop :=
  ∀ i, (∀ r : B.A, IsIntegral K.O r → (al K a ^ (p i + N)) • (e i * r) ∈ M) ∧
    ∀ m ∈ M, IsIntegral K.O ((al K a ^ (-p i)) • (e i * m))

def chi (e : ι → B.A) (I : Finset ι) (y : B.A) : ℚ :=
  K.eta (Algebra.norm K.E (y * eS B e I + (1 - eS B e I)))

def IsPre [Fintype ι] (e : ι → B.A) (S : Finset ι) : Prop :=
  CompleteOrthogonalIdempotents e ∧ ∀ i, ∃ f : B.A, IsIdempotentElem f ∧ f ≠ 0 ∧
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
    (i ∈ S → e i = f ∧ B.σ f = f) ∧ (i ∉ S → f * B.σ f = 0 ∧ e i = f + B.σ f)

def IsFrame [Fintype ι] (e π : ι → B.A) (S : Finset ι) : Prop :=
  IsPre B e S ∧ ∀ i ∈ S, B.Plus (π i) ∧ π i * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E (π i)) = -1

def Win (I I' : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i, -(L : ℤ) ≤ p i ∧ p i ≤ 2 * k + L ∧ (i ∈ I → 2 * (k : ℤ) - L ≤ p i) ∧ (i ∈ I' → p i ≤ L)

def Mid (S : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i ∉ S, (L : ℤ) ≤ p i ∧ p i ≤ 2 * k - L

theorem eta_mul {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy), neg_add, zpow_add₀ (by norm_num)]

theorem eta_sq (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]; simp

theorem abs_eta (x : K.E) : |K.eta x| = 1 := by
  unfold UQ.eta; simp

theorem abs_indM (M : Submodule K.O B.A) (y : B.A) : |indM B M y| ≤ 1 := by
  unfold indM; split_ifs <;> simp

theorem abs_indD (M : Submodule K.O B.A) (y : B.A) : |indD B M y| ≤ 1 := by
  unfold indD; split_ifs <;> simp

theorem abs_dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (hf : ∀ y, |f y| ≤ 1) (y : A) :
    |dlt π I f y| ≤ 2 ^ I.card := by
  unfold dlt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ J ∈ I.powerset, |(-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)| ≤ ∑ J ∈ I.powerset, (1 : ℚ) :=
        Finset.sum_le_sum fun J _ => by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hf _
    _ = 2 ^ I.card := by simp [Finset.card_powerset]

theorem abs_term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) :
    |term B π I I' u s M| ≤ 2 ^ I.card * 2 ^ I'.card := by
  unfold term
  rw [abs_mul]
  exact mul_le_mul (abs_dlt _ _ _ (abs_indM B M) _) (abs_dlt _ _ _ (abs_indD B M) _) (abs_nonneg _) (by positivity)

theorem dlt_eq_zero {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) (i : ι) (hi : i ∈ I)
    (h : ∀ J ⊆ I.erase i, f (π i * ((∏ j ∈ J, π j) * y)) = f ((∏ j ∈ J, π j) * y)) : dlt π I f y = 0 := by
  unfold dlt
  rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i I)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun J hJ => ?_
  have hJ' : i ∉ J := fun h => Finset.notMem_erase i I (Finset.mem_powerset.1 hJ h)
  rw [Finset.prod_insert hJ', Finset.card_insert_of_notMem hJ', mul_assoc, h J (Finset.mem_powerset.1 hJ)]
  ring

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
section
noncomputable section
namespace GlobalTheory.UnimodMass
variable {G : Type*} [Group G]

def dcMapLe {Γ W K : Subgroup G} (hWK : W ≤ K) : DC Γ W → DC Γ K :=
  Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)

def dcOfCoset (Γ W K : Subgroup G) (t : G) : K ⧸ W.subgroupOf K → DC Γ W :=
  Quotient.lift (fun k : K => (Quotient.mk (dcSetoid Γ W) (t * k))) (by
    intro a b hab
    apply Quotient.sound
    have h := (QuotientGroup.leftRel_apply).1 hab
    rw [Subgroup.mem_subgroupOf] at h
    refine ⟨1, Γ.one_mem, (a : G)⁻¹ * b, by simpa using h, ?_⟩
    simp [mul_assoc])

theorem dcOfCoset_mk (Γ W K : Subgroup G) (t : G) (k : K) :
    dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) = Quotient.mk (dcSetoid Γ W) (t * k) := rfl

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass

theorem fiber_card_mul_stabCard {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K) (t : G)
    (ht : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) (k : K) :
    Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} *
      stabCard Γ W (t * k) = stabCard Γ K t := by
  classical
  set A := {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}
  set B := {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)}
  set T := {δ : Γ // (t * k)⁻¹ * (δ : G) * (t * k) ∈ W}
  have hT : stabCard Γ W (t * k) = Nat.card T := rfl
  have hA : stabCard Γ K t = Nat.card A := rfl
  let φ : A → K := fun γ => ⟨t⁻¹ * (γ.1 : G) * t, γ.2⟩
  have hα : ∀ γ : A, dcOfCoset Γ W K t ((φ γ * k : K) : K ⧸ W.subgroupOf K) =
      dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
    intro γ
    rw [dcOfCoset_mk, dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨(γ.1 : G)⁻¹, Γ.inv_mem γ.1.2, 1, W.one_mem, ?_⟩
    simp [φ, mul_assoc]
  let α : A → B := fun γ => ⟨(φ γ * k : K), hα γ⟩
  have hsurj : Function.Surjective α := by
    rintro ⟨x, hx⟩
    induction x using QuotientGroup.induction_on with
    | H k' =>
      rw [dcOfCoset_mk, dcOfCoset_mk] at hx
      obtain ⟨γ, hγ, w, hw, e⟩ := Quotient.exact hx

      have hmem : t⁻¹ * γ⁻¹ * t ∈ K := by
        have : t⁻¹ * γ⁻¹ * t = (k' : G) * w * (k : G)⁻¹ := by
          have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
            calc (k : G) = t⁻¹ * (t * k) := by group
              _ = _ := by rw [e]; group
          rw [e']; group
        rw [this]
        exact K.mul_mem (K.mul_mem k'.2 (hWK hw)) (K.inv_mem k.2)
      refine ⟨⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩, ?_⟩
      apply Subtype.ext
      show ((φ _ * k : K) : K ⧸ W.subgroupOf K) = (k' : K ⧸ W.subgroupOf K)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
        calc (k : G) = t⁻¹ * (t * k) := by group
          _ = _ := by rw [e]; group
      have : ((φ ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩ * k)⁻¹ * k' : K) = (w⁻¹ : G) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
        rw [e']; group
      rw [this]; exact W.inv_mem hw
  have hfib : ∀ γ₀ : A, Nonempty ({γ : A // α γ = α γ₀} ≃ T) := by
    intro γ₀
    have key : ∀ γ : A, α γ = α γ₀ ↔ (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) ∈ W := by
      intro γ
      rw [Subtype.ext_iff]
      show ((φ γ * k : K) : K ⧸ W.subgroupOf K) = ((φ γ₀ * k : K) : K ⧸ W.subgroupOf K) ↔ _
      rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((φ γ₀ * k)⁻¹ * (φ γ * k) : K) : G) = (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]; group
      rw [this]
    refine ⟨{ toFun := fun γ => ⟨⟨(γ₀.1 : G)⁻¹ * γ.1.1, Γ.mul_mem (Γ.inv_mem γ₀.1.2) γ.1.1.2⟩, (key γ.1).1 γ.2⟩
              invFun := fun δ => ⟨⟨⟨(γ₀.1 : G) * δ.1, Γ.mul_mem γ₀.1.2 δ.1.2⟩, ?_⟩, ?_⟩
              left_inv := fun γ => by ext; simp
              right_inv := fun δ => by ext; simp }⟩
    · have h1 : t⁻¹ * ((γ₀.1 : G) * δ.1) * t =
          (t⁻¹ * γ₀.1 * t) * ((k : G) * ((t * k)⁻¹ * δ.1 * (t * k)) * (k : G)⁻¹) := by group
      rw [h1]
      exact K.mul_mem γ₀.2 (K.mul_mem (K.mul_mem k.2 (hWK δ.2)) (K.inv_mem k.2))
    · rw [key]
      simpa using δ.2
  have e : A ≃ B × T :=
    (Equiv.sigmaFiberEquiv α).symm.trans
      ((Equiv.sigmaCongrRight (fun b => by
          have hb := hsurj b
          exact Classical.choice (by
            obtain ⟨γ₀, hγ₀⟩ := hb
            subst hγ₀
            exact hfib γ₀))).trans (Equiv.sigmaEquivProd B T))
  rw [hT, hA, Nat.card_congr e, Nat.card_prod]

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass
open scoped BigOperators

theorem dcOfCoset_surj {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (d : DC Γ W) (hd : dcMapLe hWK d = Quotient.mk (dcSetoid Γ K) t) :
    ∃ k : K, d = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
  induction d using Quotient.inductionOn with
  | h g =>
    have h2 : (dcSetoid Γ K) g t := Quotient.exact hd
    obtain ⟨γ, hγ, κ, hκ, e⟩ := (dcSetoid Γ K).iseqv.symm h2
    refine ⟨⟨κ, hκ⟩, ?_⟩
    rw [dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨γ⁻¹, Γ.inv_mem hγ, 1, W.one_mem, ?_⟩
    simp [e, mul_assoc]

theorem dcMapLe_dcOfCoset {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (x : K ⧸ W.subgroupOf K) : dcMapLe hWK (dcOfCoset Γ W K t x) = Quotient.mk (dcSetoid Γ K) t := by
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [dcOfCoset_mk]
    apply Quotient.sound
    exact ⟨1, Γ.one_mem, (k : G)⁻¹, K.inv_mem k.2, by simp⟩

theorem mass_eq_relIndex_mul {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K)
    (hW : Finite (DC Γ W)) (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    W.relIndex K ≠ 0 ∧ mass Γ W = (W.relIndex K : ℚ) * mass Γ K := by
  classical
  haveI := hW
  haveI : Finite (DC Γ K) := finite_dc_of_le hWK

  have hfibre : ∀ d : DC Γ W, Finite {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K 1 x = d} := by
    intro d
    by_cases hne : ∃ x : K ⧸ W.subgroupOf K, dcOfCoset Γ W K 1 x = d
    · obtain ⟨x, rfl⟩ := hne
      induction x using QuotientGroup.induction_on with
      | H k =>
        have h1 := fiber_card_mul_stabCard Γ W K hWK 1 (hfin 1) k
        have h2 := stabCard_pos (Γ := Γ) (K := K) 1 (hfin 1)
        have h3 : 0 < Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)} := by
          rcases Nat.eq_zero_or_pos (Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)}) with h | h
          · rw [h, zero_mul] at h1; omega
          · exact h
        exact (Nat.card_pos_iff.1 h3).2
    · push_neg at hne
      exact Finite.of_injective (β := Empty) (fun x => (hne x.1 x.2).elim) (fun x => (hne x.1 x.2).elim)
  haveI : Finite (K ⧸ W.subgroupOf K) :=
    Finite.of_equiv _ (Equiv.sigmaFiberEquiv (dcOfCoset Γ W K 1))
  have hidx : W.relIndex K = Nat.card (K ⧸ W.subgroupOf K) := rfl
  have hne0 : W.relIndex K ≠ 0 := by
    rw [hidx]; exact Nat.card_ne_zero.2 ⟨⟨(1 : K)⟩, inferInstance⟩
  refine ⟨hne0, ?_⟩
  haveI := Fintype.ofFinite (DC Γ W)
  haveI := Fintype.ofFinite (DC Γ K)
  haveI := Fintype.ofFinite (K ⧸ W.subgroupOf K)

  have hfib : ∀ c : DC Γ K,
      ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c), ((stabCard Γ W d.out : ℕ) : ℚ)⁻¹ =
        (W.relIndex K : ℚ) * ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹ := by
    intro c
    set t := c.out with htdef
    have hct : c = Quotient.mk (dcSetoid Γ K) t := (Quotient.out_eq c).symm
    have hsK : (0 : ℚ) < stabCard Γ K t := by exact_mod_cast stabCard_pos t (hfin t)
    have hcard : (W.relIndex K : ℚ) = ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c),
        ((Finset.univ.filter (fun x => dcOfCoset Γ W K t x = d)).card : ℚ) := by
      rw [hidx, Nat.card_eq_fintype_card, ← Finset.card_univ]
      rw [Finset.card_eq_sum_card_fiberwise (f := dcOfCoset Γ W K t)
        (t := Finset.univ.filter (fun d => dcMapLe hWK d = c))]
      · push_cast; rfl
      · intro x _
        simp [dcMapLe_dcOfCoset, hct]
    rw [hcard, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    obtain ⟨k, rfl⟩ := dcOfCoset_surj hWK t _ (hd.trans hct)
    have h1 := fiber_card_mul_stabCard Γ W K hWK t (hfin t) k
    rw [dcOfCoset_mk, stabCard_out]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← dcOfCoset_mk]
    have hsW : (0 : ℚ) < stabCard Γ W (t * k) := by
      have := stabCard_pos t (hfin t)
      rcases Nat.eq_zero_or_pos (stabCard Γ W (t * k)) with h | h
      · rw [h, mul_zero] at h1; omega
      · exact_mod_cast h
    have h1' : (Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x =
        dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} : ℚ) * stabCard Γ W (t * k) = stabCard Γ K t := by
      exact_mod_cast h1
    field_simp
    linarith [h1']
  unfold mass
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ (dcMapLe hWK)]
  exact Finset.sum_congr rfl (fun c _ => hfib c)

end GlobalTheory.UnimodMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtIn
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem units_near_one_inverse_continuousAt (F K : Type) [NontriviallyNormedField F] [CommRing K] [Algebra F K]
    [Module.Finite F K] [TopologicalSpace K] [IsModuleTopology F K] [IsTopologicalRing K] :
    (∀ᶠ a in 𝓝 (1 : K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : K) := by
  classical
  let b := Module.finBasis F K
  let ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F := Algebra.leftMulMatrix b
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMap ι.toLinearMap
  have hdet : Continuous fun a : K => (ι a).det := (continuous_id.matrix_det).comp hι
  have h1 : (ι 1).det ≠ 0 := by simp
  have hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0 :=
    hdet.continuousAt.eventually_ne h1
  have hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a := by
    intro a ha
    have hn : Algebra.norm F a ≠ 0 := by rw [Algebra.norm_eq_matrix_det b]; exact ha
    rw [Algebra.norm_apply] at hn
    have hu : IsUnit (Algebra.lmul F K a) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact hn.isUnit
    obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact IsUnit.of_mul_eq_one c (by simpa using hc)
  have hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a := hev.mono hunit
  refine ⟨hev', ?_⟩
  let g : K → K := fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)
  have hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a) := by
    intro a ha
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  have heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse := by
    filter_upwards [hev'] with a ha
    simp only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  refine ContinuousAt.congr ?_ heq
  have hsymm : Continuous b.equivFun.symm := LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hdet1 : ContinuousAt Ring.inverse (ι 1).det := by
    have : (ι 1).det = 1 := by simp
    rw [this]
    have : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
    rw [this]
    exact continuousAt_inv₀ one_ne_zero
  have hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1 :=
    (continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt
  have hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1 :=
    continuous_id.matrix_mulVec continuous_const
  exact hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)

theorem et_units_near_one_inverse_continuousAt :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  fun F _ _ _ _ _ A => units_near_one_inverse_continuousAt F A.K

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolution
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem exists_aeval_eq_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) (a : A) :
    ∃ f : E[X], a = aeval g f := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm0 : minpoly E g ≠ 0 := minpoly.ne_zero hint
  have hf : aeval (LinearMap.mulLeft E g) (minpoly E g) = 0 := by
    have := aeval_algHom_apply (Algebra.lmul E A) g (minpoly E g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hn : 0 < Module.finrank E A := Module.finrank_pos
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  have h2 : (LinearMap.mulLeft E g).charpoly ∣ minpoly E g :=
    (hP.squarefree.dvd_pow_iff_dvd hn.ne').1 h1
  have h3 : Module.finrank E A ≤ (minpoly E g).natDegree := by
    have := natDegree_le_of_dvd h2 hm0
    rwa [LinearMap.charpoly_natDegree] at this
  have hli := linearIndependent_pow (K := E) g
  have h4 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h4
  haveI : Nonempty (Fin (minpoly E g).natDegree) := ⟨⟨0, by omega⟩⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; omega)
  have hle : Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin E {g}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hg : g ∈ Algebra.adjoin E {g} := Algebra.subset_adjoin (Set.mem_singleton g)
    exact Subalgebra.pow_mem (Algebra.adjoin E {g}) hg (i : ℕ)
  have ha : a ∈ Algebra.adjoin E {g} := by
    have : a ∈ Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) := by
      rw [htop]; trivial
    exact hle this
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, hf.symm⟩

theorem InvAlg.exists_aeval_eq_of_separable :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f :=
  fun _ B hP a => exists_aeval_eq_of_charpoly_separable B.g hP a

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHaarQuotientIntegralFormula
section
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR


open TopologicalGroup in
theorem integral_inducedMeasure_complex {A B C : Type} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup A]
    [IsTopologicalGroup B] [IsTopologicalGroup C] [T2Space B] [LocallyCompactSpace B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] [MeasurableSpace C]
    [BorelSpace C] {φ : A →* B} {ψ : B →* C} (H : IsSES φ ψ) (ν : Measure A) [ν.IsHaarMeasure]
    (μC : Measure C) [μC.IsHaarMeasure] (F : CompactlySupportedContinuousMap B ℂ) :
    ∫ b, F b ∂(H.inducedMeasure ν μC) = ∫ c, H.pushforward ν F c ∂μC := by
  have key : ∀ L : ℂ →L[ℝ] ℝ, L (∫ b, F b ∂(H.inducedMeasure ν μC))
      = L (∫ c, H.pushforward ν F c ∂μC) := by
    intro L
    let G : CompactlySupportedContinuousMap B ℝ :=
      ⟨⟨fun b => L (F b), L.continuous.comp F.continuous⟩,
        F.hasCompactSupport.comp_left (g := L) (map_zero L)⟩
    rw [← L.integral_comp_comm F.integrable,
      ← L.integral_comp_comm (H.pushforward ν F).integrable]
    have h1 := H.integral_inducedMeasure ν μC G
    rw [IsSES.integrate_apply] at h1
    refine h1.trans ?_
    congr with c
    rw [IsSES.pushforward_def, IsSES.pushforward_def,
      ← L.integral_comp_comm (H.pullback F _).integrable]
    simp only [IsSES.pullback_def]
    rfl
  exact Complex.ext (key Complex.reCLM) (key Complex.imCLM)

theorem exists_haar_quotient_integral_formula : ∀ (A B C : Type) [Group A] [Group B] [Group C] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C] [T2Space B] [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] [MeasurableSpace C] [BorelSpace C] (φ : A →* B) (ψ : B →* C), TopologicalGroup.IsSES φ ψ → ∀ (μB : Measure B) (μC : Measure C), μB.IsHaarMeasure → μC.IsHaarMeasure → ∃ ν : Measure A, ν.IsHaarMeasure ∧ ∀ f : B → ℂ, Continuous f → HasCompactSupport f → ∀ s : C → B, (∀ c, ψ (s c) = c) → ∫ b, f b ∂μB = ∫ c, ∫ a, f (s c * φ a) ∂ν ∂μC := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ψ H μB μC hB hC
  have : LocallyCompactSpace A := H.isClosedEmbedding.locallyCompactSpace
  let ν0 : Measure A := Measure.haar
  set μ := H.inducedMeasure ν0 μC with hμ
  have hsm := Measure.isMulLeftInvariant_eq_smul μB μ
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure μB μ
  set k := Measure.haarScalarFactor μB μ with hk
  refine ⟨k • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hpos.ne', ?_⟩
  intro f hf hfc s hs
  let F : CompactlySupportedContinuousMap B ℂ := ⟨⟨f, hf⟩, hfc⟩
  have h := integral_inducedMeasure_complex H ν0 μC F
  rw [hsm, integral_smul_nnreal_measure]
  simp_rw [integral_smul_nnreal_measure, NNReal.smul_def]
  rw [integral_smul]
  congr 1
  refine h.trans ?_
  congr with c
  conv_lhs => rw [← hs c]
  rw [H.pushforward_apply_apply]
  simp only [TopologicalGroup.IsSES.pullback_def]
  rfl

end GlobalTheory.JR
end

