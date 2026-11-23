module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankGraphJetsLeChoose
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.JetDim

theorem mem_of_formallyEtale {K R F : Type} [Field K] [CommRing R] [Field F] [Algebra F K]
    [Algebra.IsSeparable F K] (φ : K →+* R) (B : Subring R)
    (hF : ∀ c : F, φ (algebraMap F K c) ∈ B) (N : Ideal R) (hN : IsNilpotent N)
    (σ : K →+* B) (hσ : ∀ a, φ a - σ a ∈ N) (a : K) : φ a ∈ B := by
  haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let iB : F →+* B := (φ.comp (algebraMap F K)).codRestrict B hF
  letI : Algebra F B := iB.toAlgebra
  letI : Algebra F R := (φ.comp (algebraMap F K)).toAlgebra
  let I : Ideal B := N.comap B.subtype
  have hI : IsNilpotent I := by
    obtain ⟨n, hn⟩ := hN
    refine ⟨n, ?_⟩
    have h1 : I ^ n ≤ (N ^ n).comap B.subtype := Ideal.le_comap_pow _ n
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro x hx
    have := h1 hx
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_comap, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact Subtype.ext this
  let g : K →ₐ[F] B ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp σ
      commutes' := fun c => by
        change Ideal.Quotient.mk I (σ (algebraMap F K c)) = Ideal.Quotient.mk I (iB c)
        rw [Ideal.Quotient.eq, Ideal.mem_comap, map_sub]
        have := N.neg_mem (hσ (algebraMap F K c))
        convert this using 1
        simp [iB] }
  let ψ : K →ₐ[F] B := Algebra.FormallySmooth.lift I hI g
  let ψR : K →ₐ[F] R :=
    { toRingHom := B.subtype.comp ψ.toRingHom
      commutes' := fun c => by
        change B.subtype (ψ (algebraMap F K c)) = φ (algebraMap F K c)
        rw [ψ.commutes]
        rfl }
  let φF : K →ₐ[F] R := { toRingHom := φ, commutes' := fun c => rfl }
  have e : ψR = φF := by
    refine Algebra.FormallyUnramified.ext N hN (fun x => ?_)
    have h1 := Algebra.FormallySmooth.mk_lift I hI g x
    change Ideal.Quotient.mk I (ψ x) = Ideal.Quotient.mk I (σ x) at h1
    rw [Ideal.Quotient.eq, Ideal.mem_comap, map_sub] at h1
    rw [Ideal.Quotient.eq]
    have := N.sub_mem h1 (hσ x)
    convert this using 1
    change (ψ x : R) - φ x = _
    simp only [Subring.coe_subtype]
    ring
  have := DFunLike.congr_fun e a
  change (ψ a : R) = φ a at this
  rw [← this]
  exact (ψ a).2

end GlobalTheory.JetDim

namespace GlobalTheory.JetDim

theorem jets_finrank_le : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k M : ℕ) (ρ : κ →ₐ[ℂ] κ'),
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra;
  Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) ≤
    (M + k - 1).choose k ∧
  Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) := by
  intro κ κ' _ _ _ _ k M ρ hz0
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra
  obtain ⟨z, hz⟩ := hz0
  set J := RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) with hJ
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · haveI : Subsingleton ((κ ⊗[ℂ] κ') ⧸ J ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
    exact ⟨by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _, inferInstance⟩
  let mk : κ ⊗[ℂ] κ' →+* (κ ⊗[ℂ] κ') ⧸ J ^ M := Ideal.Quotient.mk (J ^ M)
  let φ : κ →+* (κ ⊗[ℂ] κ') ⧸ J ^ M := mk.comp Algebra.TensorProduct.includeLeftRingHom
  let N : Ideal ((κ ⊗[ℂ] κ') ⧸ J ^ M) := J.map mk
  have hNM : N ^ M = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have hN : IsNilpotent N := ⟨M, by rw [Ideal.zero_eq_bot]; exact hNM⟩
  have hφσ : ∀ a, φ a - algebraMap κ' _ (ρ a) ∈ N := by
    intro a
    have e : φ a - algebraMap κ' _ (ρ a) = mk (a ⊗ₜ 1 - 1 ⊗ₜ ρ a) := by rw [map_sub]; rfl
    rw [e]
    refine Ideal.mem_map_of_mem _ ?_
    simp [hJ, RingHom.mem_ker, Algebra.TensorProduct.productMap_apply_tmul]
  let t : Fin k → (κ ⊗[ℂ] κ') ⧸ J ^ M := fun i => φ (z i) - algebraMap κ' _ (ρ (z i))
  let B : Subalgebra κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M) := Algebra.adjoin κ' (Set.range t)
  have hzB : ∀ i, φ (z i) ∈ B := by
    intro i
    have : φ (z i) = t i + algebraMap κ' _ (ρ (z i)) := by simp [t]
    rw [this]
    exact B.add_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (B.algebraMap_mem _)

  let F : IntermediateField ℂ κ :=
    { carrier := {a | φ a ∈ B}
      mul_mem' := fun {a b} ha hb => by
        show φ (a * b) ∈ B
        rw [map_mul]; exact B.mul_mem ha hb
      one_mem' := by show φ 1 ∈ B; rw [map_one]; exact B.one_mem
      add_mem' := fun {a b} ha hb => by
        show φ (a + b) ∈ B
        rw [map_add (f := _)]; exact B.add_mem ha hb
      zero_mem' := by show φ 0 ∈ B; rw [map_zero]; exact B.zero_mem
      algebraMap_mem' := fun r => by
        show φ (algebraMap ℂ κ r) ∈ B
        have : φ (algebraMap ℂ κ r) = algebraMap κ' _ (algebraMap ℂ κ' r) := by
          show mk (algebraMap ℂ κ r ⊗ₜ 1) = mk (1 ⊗ₜ algebraMap ℂ κ' r)
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        rw [this]; exact B.algebraMap_mem _
      inv_mem' := fun a ha => by
        show φ a⁻¹ ∈ B
        by_cases ha0 : a = 0
        · rw [ha0, inv_zero, map_zero]; exact B.zero_mem
        have ha' : φ a ∈ B := ha
        have hnil : IsNilpotent ((⟨φ a, ha'⟩ : B) - algebraMap κ' B (ρ a)) := by
          refine ⟨M, Subtype.ext ?_⟩
          have h2 := Ideal.pow_mem_pow (hφσ a) M
          rw [hNM, Ideal.mem_bot] at h2
          simpa using h2
        have hu : IsUnit (algebraMap κ' B (ρ a)) :=
          (isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 ha0)).map _
        have hx : IsUnit (⟨φ a, ha'⟩ : B) := by
          have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
          simpa using this
        obtain ⟨y, hy⟩ := hx.exists_right_inv
        have hy' : φ a * (y : (κ ⊗[ℂ] κ') ⧸ J ^ M) = 1 := congrArg Subtype.val hy
        have h2 : φ a⁻¹ * φ a = 1 := by rw [← map_mul, inv_mul_cancel₀ ha0, map_one]
        have : φ a⁻¹ = y := by
          calc φ a⁻¹ = φ a⁻¹ * (φ a * y) := by rw [hy', mul_one]
          _ = y := by rw [← mul_assoc, h2, one_mul]
        rw [this]; exact y.2 }
  have hle : IntermediateField.adjoin ℂ (Set.range z) ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hzB i
  have eAlg : (algebraMap ℂ κ).toAlgebra = ‹Algebra ℂ κ› := Algebra.algebra_ext _ _ fun _ => rfl
  have hz' : IsTranscendenceBasis ℂ z := by
    unfold TrBasis at hz
    rw [eAlg] at hz
    exact hz
  haveI := hz'.isAlgebraic_field
  letI : Algebra (IntermediateField.adjoin ℂ (Set.range z)) F :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin ℂ (Set.range z)) F κ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic F κ :=
    Algebra.IsAlgebraic.extendScalars (R := IntermediateField.adjoin ℂ (Set.range z))
      (IntermediateField.inclusion_injective hle)
  haveI : Algebra.IsSeparable F κ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let σ : κ →+* B.toSubring :=
    ((algebraMap κ' _).comp ρ.toRingHom).codRestrict B.toSubring (fun a => B.algebraMap_mem _)
  have key : ∀ a, φ a ∈ B := fun a =>
    mem_of_formallyEtale φ B.toSubring (fun c : F => c.2) N hN σ (fun a => hφσ a) a
  have hB : ∀ x, x ∈ B := by
    intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact B.zero_mem
    | tmul a b =>
      have : Ideal.Quotient.mk (J ^ M) (a ⊗ₜ b) = φ a * algebraMap κ' _ b := by
        show mk _ = mk (a ⊗ₜ 1) * mk (1 ⊗ₜ b)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]; exact B.mul_mem (key a) (B.algebraMap_mem b)
    | add x y hx hy => rw [map_add (f := _)]; exact B.add_mem hx hy

  have ht : ∀ i, t i ∈ N := fun i => hφσ (z i)
  let f : Sym (Fin (k + 1)) (M - 1) → (κ ⊗[ℂ] κ') ⧸ J ^ M :=
    fun s => ∏ i : Fin k, t i ^ ((s : Multiset (Fin (k + 1))).count i.castSucc)
  have hmono : ∀ y ∈ Submonoid.closure (Set.range t), ∃ α : Fin k → ℕ, y = ∏ i, t i ^ α i := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨Pi.single i 1, by simp [Pi.single_apply, pow_ite]⟩
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨α, rfl⟩ := hx
      obtain ⟨β, rfl⟩ := hy
      exact ⟨α + β, by simp [pow_add, Finset.prod_mul_distrib]⟩
  have hspan : ∀ x, x ∈ Submodule.span κ' (Set.range f) := by
    intro x
    have hx : x ∈ Subalgebra.toSubmodule B := hB x
    rw [Algebra.adjoin_eq_span] at hx
    refine Submodule.span_le.2 ?_ hx
    intro y hy
    obtain ⟨α, rfl⟩ := hmono y hy
    by_cases hα : ∑ i, α i < M
    · let g : Fin (k + 1) → ℕ := Fin.snoc α (M - 1 - ∑ i, α i)
      let m : Multiset (Fin (k + 1)) := Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm g)
      have hcard : Multiset.card m = M - 1 := by
        simp only [m, Finsupp.card_toMultiset]
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        change ∑ j, g j = M - 1
        rw [Fin.sum_univ_castSucc]
        simp only [g, Fin.snoc_castSucc, Fin.snoc_last]
        omega
      refine Submodule.subset_span ⟨⟨m, hcard⟩, ?_⟩
      simp only [f]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [m, g, Finsupp.count_toMultiset]
    · have h1 : ∏ i, t i ^ α i ∈ ∏ i : Fin k, N ^ α i :=
        Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ht i) _
      rw [Finset.prod_pow_eq_pow_sum] at h1
      have h2 := Ideal.pow_le_pow_right (not_lt.1 hα) h1
      rw [hNM, Ideal.mem_bot] at h2
      rw [h2]
      exact Submodule.zero_mem _
  have htop : Submodule.span κ' (Set.range f) = ⊤ := eq_top_iff.2 fun x _ => hspan x
  refine ⟨?_, ⟨htop ▸ Submodule.fg_span (Set.finite_range f)⟩⟩
  calc Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M)
      = Module.finrank κ' (⊤ : Submodule κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M)) := (finrank_top _ _).symm
    _ = Module.finrank κ' (Submodule.span κ' (Set.range f)) := by rw [htop]
    _ ≤ Fintype.card (Sym (Fin (k + 1)) (M - 1)) := finrank_range_le_card f
    _ = (M + k - 1).choose k := by
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      have e : k + 1 + (M - 1) - 1 = M + k - 1 := by omega
      rw [e]
      exact Nat.choose_symm_of_eq_add (by omega)

end GlobalTheory.JetDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumParabolicQuotientFubini
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem split_quotient_finsum_regroup : ∀ (P M N V : Type) [Group P] [Group M] [Group N] [AddCommMonoid V] (lev : P →* M) (s : M →* P) (u : N →* P), (∀ m, lev (s m) = m) → (∀ x, lev (u x) = 1) → Function.Injective u → (∀ p, lev p = 1 → ∃ x, u x = p) → ∀ (UP : Subgroup P) (UM : Subgroup M), UM.map s ≤ UP → UP.map lev ≤ UM → ∀ (Φ : P → V), (∀ p, ∀ q ∈ UP, Φ (p * q) = Φ p) → {q : P ⧸ UP | Φ q.out ≠ 0}.Finite → ∑ᶠ q : P ⧸ UP, Φ q.out = ∑ᶠ c : M ⧸ UM, ∑ᶠ x : N ⧸ UP.comap u, Φ (s c.out * u x.out) := by
  intro P M N V _ _ _ _ lev s u hsec hlu _hu_inj hker UP UM hsU hlevU Φ hΦ hfin
  let F : (M ⧸ UM) × (N ⧸ UP.comap u) → P ⧸ UP :=
    fun cx => (QuotientGroup.mk (s cx.1.out * u cx.2.out) : P ⧸ UP)
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨c, x⟩ ⟨c', x'⟩ h
      simp only [F] at h
      rw [QuotientGroup.eq] at h
      have h1 : (c.out)⁻¹ * c'.out ∈ UM := by
        have := hlevU (Subgroup.mem_map_of_mem lev h)
        simpa [map_mul, map_inv, hsec, hlu] using this
      have hc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact QuotientGroup.eq.mpr h1
      subst hc
      have h2 : (x.out)⁻¹ * x'.out ∈ UP.comap u := by
        rw [Subgroup.mem_comap]
        have he : (s c.out * u x.out)⁻¹ * (s c.out * u x'.out) = u ((x.out)⁻¹ * x'.out) := by
          rw [map_mul, map_inv]; group
        rw [← he]; exact h
      have hx : x = x' := by
        rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
        exact QuotientGroup.eq.mpr h2
      rw [hx]
    · intro q
      set p := q.out with hp
      set c : M ⧸ UM := (QuotientGroup.mk (lev p) : M ⧸ UM) with hc
      have hk : (c.out)⁻¹ * lev p ∈ UM := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      set k := (c.out)⁻¹ * lev p with hkdef
      have hr : lev ((s c.out)⁻¹ * p * (s k)⁻¹) = 1 := by
        simp only [map_mul, map_inv, hsec, hkdef]; group
      obtain ⟨Z, hZ⟩ := hker _ hr
      refine ⟨(c, (QuotientGroup.mk Z : N ⧸ UP.comap u)), ?_⟩
      obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul (UP.comap u) Z
      simp only [F]
      rw [hy, ← QuotientGroup.out_eq' q, ← hp, QuotientGroup.eq]
      have hyU : u (y : N) ∈ UP := y.2
      have hsk : s k ∈ UP := hsU (Subgroup.mem_map_of_mem s hk)
      have he : (s c.out * u (Z * y))⁻¹ * p = (u (y : N))⁻¹ * s k := by
        rw [map_mul, hZ]; group
      rw [he]
      exact UP.mul_mem (UP.inv_mem hyU) hsk
  let e := Equiv.ofBijective F hbij
  have hval : ∀ cx, Φ (e cx).out = Φ (s cx.1.out * u cx.2.out) := by
    intro cx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul UP (s cx.1.out * u cx.2.out)
    show Φ (F cx).out = _
    simp only [F]; rw [hh]; exact hΦ _ _ h.2
  have hsupp : (Function.support
      (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))).Finite := by
    have : Function.support
        (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))
        = e ⁻¹' {q : P ⧸ UP | Φ q.out ≠ 0} := by
      ext cx; simp only [Function.mem_support, Set.mem_preimage, Set.mem_setOf_eq, hval]
    rw [this]; exact hfin.preimage e.injective.injOn
  rw [← finsum_comp_equiv e]
  rw [finsum_congr hval]
  exact finsum_curry (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out)) hsupp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdFreeTopFormEqZeroOfIsPrimeOf
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (fun i => (x i : L))) = 0 := by
  intro L _ cL Q hQ D x hx P hP
  let α : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  let ρ : Q →+* P.ring := RingHom.codRestrict Q.subtype P.ring (fun q => hP.1 q q.2)
  have hρ : ρ.comp α = P.const := RingHom.ext fun _ => Subtype.ext rfl
  have e : dForm cL (fun i => (x i : L)) = P.toRat D (dForm P.const fun i => ρ (x i)) := by
    have h := TopForm.formMap_dForm (D := D) (α := P.const) (β := cL) P.ring.subtype rfl (fun i => ρ (x i))
    refine Eq.trans ?_ h.symm
    congr 1
  let S : Submonoid Q :=
    { carrier := {b | (b : L) ≠ 0 ∧ P.ord b = 0}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_⟩
        · change (a : L) * b ≠ 0
          exact mul_ne_zero ha.1 hb.1
        · change P.ord ((a : L) * b) = 0
          rw [P.ord_mul ha.1 hb.1, ha.2, hb.2, add_zero]
      one_mem' := ⟨one_ne_zero, P.ord_one⟩ }
  letI := α.toAlgebra
  letI := P.const.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower ℂ Q P.ring := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization S P.ring :=
    { map_units := fun ⟨b, hb⟩ => by
        have hinv : (b : L)⁻¹ ∈ P.ring := by
          rw [← P.ord_nonneg_iff (inv_ne_zero hb.1), P.ord_inv, hb.2, neg_zero]
        exact IsUnit.of_mul_eq_one (⟨(b : L)⁻¹, hinv⟩ : P.ring)
          (Subtype.ext (mul_inv_cancel₀ hb.1))
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb0, hbo⟩), Subtype.ext e⟩
      exists_of_eq := fun {a b} e => by
        have h : (a : L) = b := congrArg (fun z : P.ring => (z : L)) e
        exact ⟨1, by rw [Subtype.ext h]⟩ }
  haveI : Algebra.FormallyEtale Q P.ring := .of_isLocalization S
  have hG : IsFreeGen P.ring (TopForm.formMap D ρ hρ (dForm α x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q P.ring) D)
  rw [TopForm.formMap_dForm] at hG
  rw [e]
  exact P.formOrd_toRat hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem genPair_specializes_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str,
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
        (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  intro F _ Y K _ ψ₁ ψ₂ hG
  obtain ⟨hF, V, v₁, v₂, e₁, e₂, e₃, e₄⟩ := hG
  have hs : (ratOf Y).pt ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have k : ∀ ψ : Y.Fn →+* K, (spMap ψ ≫ (ratOf Y).pt) ≫ Y.str = spMap (ψ.comp (algebraMap F Y.Fn)) :=
    fun ψ => (Category.assoc (spMap ψ) (ratOf Y).pt Y.str).trans
      ((congrArg (fun g => spMap ψ ≫ g) hs).trans (by rw [← Spec.map_comp]; rfl))
  have h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str := by
    rw [k, k, hF]
  refine ⟨h, ?_⟩
  haveI : IsDominant (spMap (algebraMap V K)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap V K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap V K) from Subtype.val_injective)]
    exact bot_le
  have hv : v₁ ≫ Y.str = v₂ ≫ Y.str := by
    refine ext_of_isDominant (spMap (algebraMap V K)) ?_
    rw [← Category.assoc, ← Category.assoc, e₁, e₂]
    exact h
  let v := Limits.pullback.lift v₁ v₂ hv
  have hgen : spMap (algebraMap V K) ≫ v =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst]; exact e₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · simp only [v, Category.assoc, Limits.pullback.lift_snd]; exact e₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hres : spMap (IsLocalRing.residue V) ≫ v =
      (spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
    · simp only [v, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id]
      exact e₃.symm
  have hsp := ClosedPt.gen_specializes v (IsLocalRing.closedPoint K)
  rw [hgen] at hsp
  have hc : v (IsLocalRing.closedPoint V) = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
    calc v (IsLocalRing.closedPoint V) = (spMap (IsLocalRing.residue V) ≫ v) (IsLocalRing.closedPoint _) :=
          (ClosedPt.closedPt_comp v).symm
      _ = ((spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str) (IsLocalRing.closedPoint _) := by
          rw [hres]
      _ = Limits.pullback.diagonal Y.str ((spMap (IsLocalRing.residue V) ≫ v₁) (IsLocalRing.closedPoint _)) :=
          Scheme.Hom.comp_apply _ _ _
      _ = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by rw [ClosedPt.closedPt_comp v₁, e₄]
  rw [hc] at hsp
  exact hsp

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePullBirationalModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isometric_pull_shiftC {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (L : HermLB p) (t : ℝ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.shift (fun _ => t) fun _ => rfl).pull π hπ).Isometric ((L.pull π hπ).shift (fun _ => t) fun _ => rfl) :=
  HermLB.isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm

theorem gdeg_pull_model : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q)
    (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧
    ∀ (a t : ℝ), L.IsSelfInter a →
      ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  intro hC k _ X Y _ _ p q D hX hY π hπ φ hM L
  have hdeg : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hM.deg]; exact one_ne_zero
  have hP := ((hC.arProj k X Y p q D hX hY π hπ hM.gen hdeg).1)
  have hP1 : ∀ (M : HermLB p) (a : ℝ), M.IsSelfInter a → (M.pull π hπ).IsSelfInter a := fun M a h => by
    have := hP M a h
    rwa [hM.deg, Nat.cast_one, one_mul] at this
  have hS := hC.arShift
  have hg : gdeg (L.pull π hπ) D = gdeg L D := by
    obtain ⟨h, hh⟩ := ((hC.arExists k X p D hX).1 L)
    have ha : L.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    set a := h (genericPoint X)

    have h1 := hP1 _ _ (hS k X p D hX L a 1 ha)
    have h1' := (isometric_pull_shiftC L 1 π hπ).isSelfInter hY h1
    have h2 := hS k Y q D hY (L.pull π hπ) a 1 (hP1 L a ha)
    have e := HermLB.IsSelfInter.unique hY h1' h2
    have hD : ((D : ℝ) + 1) ≠ 0 := by positivity
    have : ((D : ℝ) + 1) * gdeg L D = ((D : ℝ) + 1) * gdeg (L.pull π hπ) D := by linarith
    exact (mul_left_cancel₀ hD this).symm
  refine ⟨hg, fun a t ha => ?_⟩
  have := hS k Y q D hY (L.pull π hπ) a t (hP1 L a ha)
  rwa [hg] at this

end GlobalTheory.HSNef
end
end

