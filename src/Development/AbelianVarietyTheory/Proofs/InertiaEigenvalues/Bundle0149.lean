module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianDualInvAlgBaseChangeUnramifiedIff
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr.Dual

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr

theorem val_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]
  ring

theorem val_inv (K : UQ) (x : K.E) : val K.O x⁻¹ = - val K.O x := by
  unfold val
  rw [map_inv₀, WithZero.log_inv]

theorem deg_pos {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exfalso
    have h1 := K'.card_res
    rw [hU.1, h, pow_zero, one_pow] at h1
    have : 1 < Nat.card (IsLocalRing.ResidueField K'.O) := Finite.one_lt_card
    omega
  · exact h

theorem herm_eq_trace {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (x y z : B.A) :
    B.herm x y z = @Algebra.trace K.E K'.E _ _ φ.toAlgebra ((overExt φ B ψ hψ hσ).herm x y z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos
    (by rw [show Module.finrank K.E K'.E = d from hU.2.2.2.2]; exact deg_pos hU)
  haveI : Module.Finite K'.E B.A := Module.Finite.of_restrictScalars_finite K.E K'.E B.A
  show Algebra.trace K.E B.A (x * y * B.σ z) = Algebra.trace K.E K'.E (Algebra.trace K'.E B.A (x * y * B.σ z))
  exact (Algebra.trace_trace _).symm

theorem herm_smul {K K' : UQ} {φ : K.E →+* K'.E} (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (x y z : B.A) (m : K'.E) (y₀ : K'.O) (hcm : K'.c (algebraMap K'.O K'.E y₀) = m) :
    (overExt φ B ψ hψ hσ).herm x y (y₀ • (show (overExt φ B ψ hψ hσ).A from z)) =
      m * (overExt φ B ψ hψ hσ).herm x y z := by
  letI : Algebra K'.E B.A := ψ.toAlgebra
  have hs : B.σ (ψ (algebraMap K'.O K'.E y₀) * z) = ψ m * B.σ z := by
    rw [map_mul, hσ, hcm]
  show Algebra.trace K'.E B.A (x * y * B.σ (ψ (algebraMap K'.O K'.E y₀) * z)) =
    m * Algebra.trace K'.E B.A (x * y * B.σ z)
  rw [hs, show x * y * (ψ m * B.σ z) = m • (x * y * B.σ z) by
    rw [Algebra.smul_def]; show _ = ψ m * _; ring, LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.UnitLemma.Unr.Dual


open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual in
theorem GlobalTheory.UnitLemma.Unr.dual_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (x y : B.A), (∀ z ∈ L, (overExt φ B ψ hψ hσ).herm x y z ∈ (algebraMap K'.O K'.E).range) ↔ (∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) := by
  intro K K' d φ hU B ψ hψ hσ L x y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hT : ∀ z, B.herm x y z = Algebra.trace K.E K'.E ((overExt φ B ψ hψ hσ).herm x y z) :=
    fun z => herm_eq_trace hU B ψ hψ hσ x y z
  constructor
  · intro h z hz
    obtain ⟨b, hb⟩ := h z hz
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.UnitLemma.Unr.trace_int K K' d φ hU b
    refine ⟨a, ?_⟩
    calc algebraMap K.O K.E a = Algebra.trace K.E K'.E (algebraMap K'.O K'.E b) := ha.symm
      _ = Algebra.trace K.E K'.E ((overExt φ B ψ hψ hσ).herm x y z) := by rw [hb]
      _ = B.herm x y z := (hT z).symm
  · intro h z₀ hz₀
    by_contra hw
    have hv : val K'.O ((overExt φ B ψ hψ hσ).herm x y z₀) < 0 := by
      by_contra hle
      push_neg at hle
      obtain ⟨b, hb⟩ := mem_range_of_val_nonneg K' _ hle
      exact hw ⟨b, hb⟩
    have hw0 : (overExt φ B ψ hψ hσ).herm x y z₀ ≠ 0 := by
      intro h0
      exact hw ⟨0, by rw [h0, map_zero]⟩
    obtain ⟨u, a, ha, hua⟩ := GlobalTheory.T.exists_unit_trace_unramifiedInvolutionFieldExt K K' d φ hU
    obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
    have hπv : val K.O π = 1 := by
      unfold val
      rw [hπ, WithZero.log_exp]
      norm_num
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp [val] at hπv
    have hφπ : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
    set w := (overExt φ B ψ hψ hσ).herm x y z₀ with hwdef
    set m : K'.E := algebraMap K'.O K'.E u * w⁻¹ * (φ π)⁻¹ with hm
    have hm_int : 0 ≤ val K'.O m := by
      by_cases hu0 : algebraMap K'.O K'.E u = 0
      · rw [hm, hu0, zero_mul, zero_mul]
        simp [val]
      · rw [hm, val_mul K' (mul_ne_zero hu0 (inv_ne_zero hw0)) (inv_ne_zero hφπ),
          val_mul K' hu0 (inv_ne_zero hw0), val_inv, val_inv, hU.2.2.1, hπv]
        have := val_algebraMap_nonneg K' u
        omega
    obtain ⟨m₀, hm₀⟩ := mem_range_of_val_nonneg K' m hm_int
    obtain ⟨y₀, hy₀⟩ := K'.c_int m₀
    have hz₁ : y₀ • z₀ ∈ L := L.smul_mem y₀ hz₀
    have key : (overExt φ B ψ hψ hσ).herm x y (y₀ • z₀) = m * w :=
      herm_smul B ψ hψ hσ x y z₀ m y₀ (by rw [← hy₀, K'.c_c, hm₀])
    obtain ⟨b, hb⟩ := h _ hz₁
    have hb' := hb.trans (hT _)
    rw [key] at hb'
    have hmw : m * w = π⁻¹ • algebraMap K'.O K'.E u := by
      rw [Algebra.smul_def, hm]
      show _ = φ π⁻¹ * _
      rw [map_inv₀]
      field_simp
    rw [hmw, LinearMap.map_smul, hua, smul_eq_mul] at hb'
    have ha0 : algebraMap K.O K.E a ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap K.O K.E), (IsFractionRing.injective K.O K.E).eq_iff]
      exact ha.ne_zero
    have h1 := val_algebraMap_nonneg K b
    rw [hb', val_mul K (inv_ne_zero hπ0) ha0, val_inv, hπv, GlobalTheory.UnitLemma.Orbit.val_unit a ha] at h1
    omega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionFromSubgroupTrans
section
open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory.BrauerZero

theorem ind_ind_of_le {G : Type} [Group G] [Finite G] (K A : Subgroup G) (hKA : K ≤ A)
    (ψ : K → ℂ) :
    ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by
  classical
  haveI := Fintype.ofFinite G
  funext g
  have hcard : Nat.card (K.subgroupOf A) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv
  have key : ∀ a y : A, ext0 (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩) (y⁻¹ * a * y)
      = ext0 K ψ ((y : G)⁻¹ * (a : G) * y) := by
    intro a y
    have hc : ((y⁻¹ * a * y : A) : G) = (y : G)⁻¹ * (a : G) * y := by simp
    by_cases h : (y : G)⁻¹ * (a : G) * y ∈ K
    · have h' : y⁻¹ * a * y ∈ K.subgroupOf A := by rw [Subgroup.mem_subgroupOf, hc]; exact h
      rw [ext0, ext0, dite_eq_left h', dite_eq_left h]
      congr 1
    · have h' : y⁻¹ * a * y ∉ K.subgroupOf A := by rw [Subgroup.mem_subgroupOf, hc]; exact h
      rw [ext0, ext0, dite_eq_right h', dite_eq_right h]
  have step : ∀ x : G, ext0 A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) (x⁻¹ * g * x)
      = (Nat.card K : ℂ)⁻¹ * ∑ y : A, ext0 K ψ ((x * y)⁻¹ * g * (x * y)) := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ A
    · rw [ext0, dite_eq_left hx, ind, hcard, finsum_eq_sum_of_fintype]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [key ⟨_, hx⟩ y]
      congr 1
      simp only [mul_inv_rev]
      group
    · rw [ext0, dite_eq_right hx]
      symm
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
      have hn : (x * y)⁻¹ * g * (x * y) ∉ K := by
        intro hk
        apply hx
        have hA : (x * y)⁻¹ * g * (x * y) ∈ A := hKA hk
        have e : x⁻¹ * g * x = (y : G) * ((x * y)⁻¹ * g * (x * y)) * (y : G)⁻¹ := by group
        rw [e]
        exact A.mul_mem (A.mul_mem y.2 hA) (A.inv_mem y.2)
      rw [ext0, dite_eq_right hn]
  rw [ind, ind, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun x _ => step x), ← Finset.mul_sum, Finset.sum_comm]
  have shift : ∀ y : A, ∑ x : G, ext0 K ψ ((x * y)⁻¹ * g * (x * y)) = ∑ z : G, ext0 K ψ (z⁻¹ * g * z) :=
    fun y => Fintype.sum_equiv (Equiv.mulRight (y : G)) _ _ (fun x => rfl)
  rw [Finset.sum_congr rfl (fun y _ => shift y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have hA0 : (Nat.card A : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := A)).ne'
  field_simp

end GlobalTheory.BrauerZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedOneSubIndexMemDegreeOneCharacterDiff
section
open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory.BrauerZero

theorem ind_one_sub_index_mem_D0 {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hK : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  classical
  haveI := Fintype.ofFinite G
  haveI hN : K.Normal := ⟨fun n hn g => by
    have h1 := hK g n
    have : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [this]; exact K.mul_mem h1 hn⟩
  letI : CommGroup (G ⧸ K) :=
    { (inferInstance : Group (G ⧸ K)) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with
        | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have := hK b⁻¹ a⁻¹
          have e : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ := by group
          rw [e]; exact this }
  haveI : Fintype (G ⧸ K) := Fintype.ofFinite _
  let Q := Additive (G ⧸ K)

  let F : AddChar Q ℂ → G → ℂ := fun ψ g => ψ (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
  have hFmul : ∀ ψ : AddChar Q ℂ, ∀ a b : G, F ψ (a * b) = F ψ a * F ψ b := by
    intro ψ a b
    simp only [F, QuotientGroup.mk_mul, ofMul_mul, AddChar.map_add_eq_mul]
  have hFone : ∀ ψ : AddChar Q ℂ, F ψ 1 = 1 := by
    intro ψ
    simp only [F, QuotientGroup.mk_one, ofMul_one, AddChar.map_zero_eq_one]

  have hgen : ∀ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) ∈ D0 G := by
    intro ψ
    let f : G →* ℂ := { toFun := F ψ, map_one' := hFone ψ, map_mul' := hFmul ψ }
    let χ : (⊤ : Subgroup G) →* ℂˣ := (MonoidHom.toHomUnits f).comp (⊤ : Subgroup G).subtype
    have hcl : ∀ g x : G, F ψ (x⁻¹ * g * x) = F ψ g := by
      intro g x
      rw [hFmul, hFmul, mul_comm (F ψ x⁻¹), mul_assoc, ← hFmul, inv_mul_cancel, hFone, mul_one]
    have h1 : ind (⊤ : Subgroup G) (fun h => (χ h : ℂ)) = F ψ := by
      exact (ind_top (F ψ) hcl : _)
    have h2 : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) :=
      ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
    apply AddSubgroup.subset_closure
    exact ⟨⊤, χ, by rw [h1, h2]⟩

  have hind : ∀ g : G, ind K (fun _ => (1 : ℂ)) g = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have hconj : ∀ x : G, (x⁻¹ * g * x ∈ K ↔ g ∈ K) := by
      intro x
      constructor
      · intro h
        have := hN.conj_mem _ h x
        have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
        rwa [e] at this
      · intro h
        have := hN.conj_mem _ h x⁻¹
        have e : x⁻¹ * g * x⁻¹⁻¹ = x⁻¹ * g * x := by group
        rwa [e] at this
    simp only [ind, finsum_eq_sum_of_fintype, ext0]
    have hs : ∀ x : G, (if h : x⁻¹ * g * x ∈ K then (1 : ℂ) else 0) = if g ∈ K then 1 else 0 := by
      intro x
      by_cases hg : g ∈ K
      · rw [dite_eq_left ((hconj x).2 hg), if_pos hg]
      · rw [dite_eq_right (fun h => hg ((hconj x).1 h)), if_neg hg]
    rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, ← K.card_mul_index]
    have : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := K)).ne'
    split_ifs
    · push_cast; field_simp
    · simp

  have hsum : ∀ g : G, (∑ ψ : AddChar Q ℂ, F ψ g) = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have := AddChar.sum_apply_eq_ite (α := Q) (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
    simp only [F]
    rw [this]
    have hc : (Fintype.card Q : ℂ) = (K.index : ℂ) := by
      rw [Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
    have he : (Additive.ofMul (QuotientGroup.mk g : G ⧸ K) = 0) ↔ g ∈ K := by
      rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]
    by_cases hg : g ∈ K
    · rw [if_pos (he.2 hg), if_pos hg, hc]
    · rw [if_neg (fun h => hg (he.1 h)), if_neg hg]
  have hcard : (Fintype.card (AddChar Q ℂ) : ℂ) = (K.index : ℂ) := by
    rw [AddChar.card_eq, Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
  have heq : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ))
      = ∑ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) := by
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [hind g, hsum g, hcard]
  rw [heq]
  exact AddSubgroup.sum_mem _ (fun ψ _ => hgen ψ)

end GlobalTheory.BrauerZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvCupPairingOfInvCupCharacters
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

private lemma pairing_smul_left' {p : ℕ} [NeZero p] {M M' : Type} [AddCommGroup M] [AddCommGroup M']
    [Module (ZMod p) M] (β : M →+ M' →+ ZMod p) (a : ZMod p) (v : M) (m' : M') :
    β (a • v) m' = a * β v m' := by
  have h : a • v = a.val • v := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact Nat.cast_smul_eq_nsmul (ZMod p) a.val v
  rw [h, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem exists_sum_mul_of_finite_torsion (l : ℕ) [Fact l.Prime] (M M' : Type) [AddCommGroup M]
    [AddCommGroup M'] [Module (ZMod l) M] (β : M →+ M' →+ ZMod l) (S : Set M)
    (hS : S.Finite) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → M →+ ZMod l) (d : ι → M' →+ ZMod l),
      ∀ m ∈ S, ∀ m' : M', β m m' = ∑ k ∈ s, c k m * d k m' := by
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  refine ⟨_, hS.toFinset.biUnion (fun m => (b.repr m).support),
    fun i => (b.coord i).toAddMonoidHom, fun i => β (b i), ?_⟩
  intro m hm m'
  have hsub : (b.repr m).support ⊆ hS.toFinset.biUnion (fun m => (b.repr m).support) :=
    Finset.subset_biUnion_of_mem (fun m => (b.repr m).support) (hS.mem_toFinset.2 hm)
  have hm' : m = ∑ i ∈ (b.repr m).support, b.repr m i • b i := by
    conv_lhs => rw [← b.linearCombination_repr m]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  conv_lhs => rw [hm']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, AddMonoidHom.finsetSum_apply]
  simp only [pairing_smul_left', LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply]
  refine Finset.sum_subset hsub ?_
  intro k _ hk
  have hz : b.repr m k = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.2 h)
  rw [hz, zero_mul]

theorem inv_cup_pairing_of_inv_cup_characters : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (μ : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g m, μ g m = m) → ∀ (e : H2 μ →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) (I : Γ → Prop) (u : ZMod (l ^ 1)) (γ φ : Γ), (∀ z y : Γ → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = u * (z γ * y φ)) → ∀ (M M' : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M'], (∀ m : M, l • m = 0) → ∀ (β : M →+ M' →+ ZMod (l ^ 1)) (x : Γ → M) (y : Γ → M'), Continuous x → Continuous y → (∀ g h, x (g * h) = x g + x h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = β (x g) (y h)) → e (Submodule.Quotient.mk w) = u * β (x γ) (y φ) := by
  intro Γ _ _ _ _ l _ μ hμ e I u γ φ hchar M M' _ _ _ _ _ _ hl β x y hxc hyc hxa hya hyI w hw
  classical
  haveI hp : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  haveI : NeZero (l ^ 1) := ⟨hp.out.ne_zero⟩
  letI : Module (ZMod (l ^ 1)) M :=
    AddCommGroup.zmodModule (fun m => by rw [pow_one]; exact hl m)
  have hfin : (Set.range x).Finite := (isCompact_range hxc).finite_of_discrete
  obtain ⟨ι, s, c, d, hdec⟩ :=
    exists_sum_mul_of_finite_torsion (l ^ 1) M M' β (Set.range x) hfin
  have hmem : ∀ k, (fun q : Γ × Γ => c k (x q.1) * d k (y q.2)) ∈ Z2 μ := by
    intro k
    rw [mem_cocycles2]
    refine ⟨?_, ?_⟩
    · exact ((continuous_of_discreteTopology.comp hxc).comp continuous_fst).mul
        ((continuous_of_discreteTopology.comp hyc).comp continuous_snd)
    · intro g h k'
      simp only [hμ, hxa, hya, map_add (f := _)]
      ring
  let W : ι → Z2 μ := fun k => ⟨_, hmem k⟩
  have hWsum : w = ∑ k ∈ s, W k := by
    apply Subtype.ext
    funext q
    rcases q with ⟨g, h⟩
    rw [Submodule.coe_sum, Finset.sum_apply, hw g h]
    exact hdec (x g) ⟨g, rfl⟩ (y h)
  have hW : ∀ k, e (Submodule.Quotient.mk (W k)) = u * (c k (x γ) * d k (y φ)) := fun k =>
    hchar (fun g => c k (x g)) (fun g => d k (y g))
      (continuous_of_discreteTopology.comp hxc) (continuous_of_discreteTopology.comp hyc)
      (fun g h => by simp only [hxa, map_add (f := _)]) (fun g h => by simp only [hya, map_add (f := _)])
      (fun g hg => by simp only [hyI g hg, map_zero]) (W k) (fun g h => rfl)
  have hq : (Submodule.Quotient.mk (∑ k ∈ s, W k) : H2 μ) =
      ∑ k ∈ s, (Submodule.Quotient.mk (W k) : H2 μ) :=
    map_sum (Submodule.mkQ _) W s
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hWsum, hq, map_sum]
  simp only [hW]
  rw [← Finset.mul_sum, ← hdec (x γ) ⟨γ, rfl⟩ (y φ)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypMemInducedFourierWeyl
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.HypJ

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) →
    ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧
      ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  have hH : μK.IsAddHaarMeasure := hsd.1
  have hT := _root_.GlobalTheory.JR.TildeTest.main F E A ψ hψ μK hH φ' hφ
  refine ⟨⟨?_, fun z s g => _root_.GlobalTheory.JHypEquiv.jHyp_nm F E A μK hH ψ φ' z s g⟩, ?_⟩
  · obtain ⟨U, hU, hk⟩ := _root_.GlobalTheory.RowSmooth.row_smooth A.K _ hT
    refine ⟨U, hU, fun g k hkU => ?_⟩
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have := hk k hkU (t * g 1 0) (t * g 1 1)
    simp only at this
    have e1 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 =
        g 1 0 * k 0 0 + g 1 1 * k 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 =
        g 1 0 * k 0 1 + g 1 1 * k 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [e1, e2]
    rw [← this]; congr 2 <;> ring
  · intro h
    have key : ∀ c u, A.tilde μK ψ (A.fourK μK ψ φ') c u = A.tilde μK ψ φ' (-u) c := by
      intro c u
      have hG := GlobalTheory.TestFn.slice_test _ hT c
      have := hsd.2 _ hG u
      rw [← this]
      unfold Et.tilde fourB
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [_root_.GlobalTheory.FourKFub.fourK_eq_fourB_tilde F E A ψ hψ μK hH φ' hφ b c]
      unfold fourB Et.tilde Et.kerK
      rw [mul_comm u b]
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [key]
    congr 2
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]

end GlobalTheory.JR.HypJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemAdjoinGen
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem span_adjoin_gen_eq_top {K : UQ} (B : InvAlg K) (hP : B.P.Separable) :
    Submodule.span K.E ((Subalgebra.toSubmodule (Algebra.adjoin K.O {B.g}) : Submodule K.O B.A) : Set B.A) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨f, rfl⟩ := Sandwich.exists_aeval B hP x
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show B.g ^ i ∈ Algebra.adjoin K.O {B.g}
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) i

theorem pow_smul_mem_adjoin_gen : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a →
    ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  intro K B a hP ha
  obtain ⟨m, hm⟩ := Sandwich.integral_sub B hP a ha.2.1 _ (span_adjoin_gen_eq_top B hP)
  refine ⟨m, fun r hr => ?_⟩
  have h := hm m le_rfl r hr
  have e : (al K a ^ m) • r = algebraMap K.O B.A a ^ m * r := by
    rw [Algebra.smul_def, al, ← map_pow, ← map_pow, ← IsScalarTower.algebraMap_apply]
  rw [e]
  exact h

end GlobalTheory.UnitLemma.Desc
end
end

