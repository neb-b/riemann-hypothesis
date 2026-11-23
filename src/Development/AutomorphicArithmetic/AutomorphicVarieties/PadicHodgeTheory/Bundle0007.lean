module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsMonicUnitCoeffZeroAnnihilatingOfSpectrumNo
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem exists_monic_integral_unit_root {l : ℕ} [Fact l.Prime] (a : Om l) (ha : ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (X - C a) ∣ Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  have hm : (minpoly ℚ_[l] a).Monic := minpoly.monic hint
  have hs : spectralNorm ℚ_[l] (Om l) a = 1 := ha
  have hc : ∀ n, ‖(minpoly ℚ_[l] a).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hm).1 (le_of_eq hs)
  have h0 : ‖(minpoly ℚ_[l] a).coeff 0‖ = 1 := by
    have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (Om l) a
    rw [hs] at h
    have hpos : (0 : ℝ) < (minpoly ℚ_[l] a).natDegree := by
      exact_mod_cast minpoly.natDegree_pos hint
    have h2 := congrArg (fun t : ℝ => t ^ (((minpoly ℚ_[l] a).natDegree : ℕ) : ℝ)) h
    simp only [Real.one_rpow] at h2
    rw [← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one] at h2
    exact h2.symm
  have hl : minpoly ℚ_[l] a ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨Q, hQm, ?_, ?_⟩
  · rw [PadicInt.isUnit_iff]
    rw [← hQ, coeff_map] at h0
    exact h0
  · rw [← Polynomial.map_map, hQ, dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap]
    exact minpoly.aeval _ _

private theorem aux_mul {l : ℕ} [Fact l.Prime] (s : Multiset (Om l)) (hs : ∀ a ∈ s, ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (s.map (fun a => X - C a)).prod ∣
        Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, monic_one, by simp, by simp⟩
  | cons a s ih =>
    obtain ⟨Q, h1, h2, h3⟩ := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
    obtain ⟨R, g1, g2, g3⟩ := exists_monic_integral_unit_root a (hs a (Multiset.mem_cons_self a s))
    refine ⟨R * Q, g1.mul h1, ?_, ?_⟩
    · rw [mul_coeff_zero]; exact g2.mul h2
    · rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul]
      exact mul_dvd_mul g3 h3

theorem UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), (∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ‖a‖ = 1) → ∃ P : ℤ_[l][X], P.Monic ∧ IsUnit (P.coeff 0) ∧ aeval F (P.map ((algebraMap ℚ_[l] ↥L).comp (algebraMap ℤ_[l] ℚ_[l]))) = 0 := by
  intro l _ L d F hF
  set χ := (F.map (algebraMap ↥L (Om l))).charpoly with hχ
  have hχm : χ.Monic := Matrix.charpoly_monic _
  obtain ⟨Q, h1, h2, h3⟩ := aux_mul χ.roots (fun a ha =>
    hF a (Matrix.mem_spectrum_iff_isRoot_charpoly.2 ((mem_roots hχm.ne_zero).1 ha)))
  refine ⟨Q, h1, h2, ?_⟩
  rw [← (IsAlgClosed.splits χ).eq_prod_roots_of_monic hχm, hχ, Matrix.charpoly_map,
    IsScalarTower.algebraMap_eq ℚ_[l] L (Om l), RingHom.comp_assoc, ← Polynomial.map_map,
    map_dvd_map'] at h3
  obtain ⟨R, hR⟩ := h3
  rw [hR, map_mul, Matrix.aeval_self_charpoly, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteFieldEnoughRootsOfUnity
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem UpperTheory.V.Loc.finite_field_enough_roots_of_unity (k : Type) [Field k] [Finite k] :
    HasEnoughRootsOfUnity k (Nat.card kˣ) := by
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have htop : rootsOfUnity (Nat.card kˣ) k = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [mem_rootsOfUnity]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top]

private theorem UpperTheory.V.Loc.mem_closure_of_kernel_containment {G k J : Type} [Group G] [Field k] [Finite k] [Finite J]
    (χ : J → G →* kˣ) (ω : G →* kˣ) (h : ∀ g, (∀ j, χ j g = 1) → ω g = 1) :
    ω ∈ Subgroup.closure (Set.range χ) := by
  classical
  let Φ : G →* (J → kˣ) := Pi.monoidHom χ
  let A := Φ.range
  have hker : Φ.ker ≤ ω.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g fun j => congrFun hg j
  let ψ : A →* kˣ := (QuotientGroup.lift Φ.ker ω hker).comp
    (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom
  have hψ : ∀ g, ψ (Φ.rangeRestrict g) = ω g := by
    intro g
    have hs : (QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)
        = (g : G ⧸ Φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift Φ.ker ω hker
      ((QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)) = ω g
    rw [hs]
    rfl
  let e : J → (A →* kˣ) := fun j => (Pi.evalMonoidHom (fun _ : J => kˣ) j).comp A.subtype
  have he : ∀ j, (e j).comp Φ.rangeRestrict = χ j := fun j => by
    ext g
    rfl
  have hω : ω = ψ.comp Φ.rangeRestrict := by
    ext g
    rw [MonoidHom.comp_apply, hψ]
  haveI : Finite (A →* kˣ) :=
    Finite.of_injective (fun f : A →* kˣ => (f : A → kˣ)) DFunLike.coe_injective
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  haveI := UpperTheory.V.Loc.finite_field_enough_roots_of_unity k
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent A) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    refine Subtype.ext (funext fun j => ?_)
    simp [pow_card_eq_one']
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent (A →* kˣ)) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun f => ?_
    refine MonoidHom.ext fun a => ?_
    simp [pow_card_eq_one']
  have hS : ψ ∈ Subgroup.closure (Set.range e) := by
    rw [← CommGroup.forall_monoidHom_apply_eq_one_iff k]
    intro η hη
    have ha : CommGroup.monoidHomMonoidHomEquiv A k η = 1 := by
      refine Subtype.ext (funext fun j => ?_)
      have hj := CommGroup.apply_monoidHomMonoidHomEquiv k (e j) η
      rw [hη _ (Subgroup.subset_closure ⟨j, rfl⟩)] at hj
      exact hj
    rw [← CommGroup.apply_monoidHomMonoidHomEquiv k ψ η, ha, map_one]
  have key : ∀ φ ∈ Subgroup.closure (Set.range e),
      φ.comp Φ.rangeRestrict ∈ Subgroup.closure (Set.range χ) := by
    intro φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [he]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    | one =>
      rw [MonoidHom.one_comp]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [MonoidHom.mul_comp]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [MonoidHom.inv_comp]
      exact inv_mem hx
  rw [hω]
  exact key ψ hS

theorem UpperTheory.V.Loc.v0e :
    ∀ {G k ι : Type} [Group G] [Field k] [Finite k] [Finite ι] (κ : ι → G →* kˣ) (ω : G →* kˣ), (∃ g, (∀ i j, κ i g = κ j g) ∧ ω g ≠ 1) ↔ ω ∉ Subgroup.closure (Set.range fun q : ι × ι => κ q.1 / κ q.2) := by
  intro G k ι _ _ _ _ κ ω
  constructor
  · rintro ⟨g, hg, hω⟩ hmem
    apply hω
    refine Subgroup.closure_induction (p := fun x _ => x g = 1) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨q, rfl⟩
      simp [hg q.1 q.2]
    · rfl
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro x _ hx
      simp [hx]
  · intro hn
    by_contra hc
    apply hn
    refine UpperTheory.V.Loc.mem_closure_of_kernel_containment _ ω fun g hg => ?_
    by_contra hne
    refine hc ⟨g, fun i j => ?_, hne⟩
    have := hg (i, j)
    simpa [div_eq_one] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem fd_pow_root {K : Type*} [Field K] {m n : ℕ} {y : K} (h : y ^ m = 1) :
    (y ^ n) ^ m = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

private theorem fd_level {v : ℕ} [Fact v.Prime] {x : Om v} (hx : x ∈ MaximalUnramifiedExtension v) :
    ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g x = h x := by
  have hv : v.Prime := Fact.out
  have key : ∀ {a b : Om v},
      (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g a = h a) →
      (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g b = h b) →
      ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) →
        g a = h a ∧ g b = h b := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, fun h => (hv.dvd_mul.mp h).elim hm hn, fun g h hgh => ⟨ha g h fun y hy => ?_,
      hb g h fun y hy => ?_⟩⟩
    · exact hgh y (by rw [pow_mul, hy, one_pow])
    · exact hgh y (by rw [mul_comm, pow_mul, hy, one_pow])
  unfold MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, -, hm, hx⟩ := hx
    exact ⟨m, hm, fun g h hgh => hgh x hx⟩
  | algebraMap x =>
    exact ⟨1, hv.not_dvd_one, fun g h _ => by rw [AlgEquiv.commutes, AlgEquiv.commutes]⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, h⟩ := key hx hy
    exact ⟨m, hm, fun g k hgk => by rw [map_add (f := _), map_add (f := _), (h g k hgk).1, (h g k hgk).2]⟩
  | inv x _ hx =>
    obtain ⟨m, hm, h⟩ := hx
    exact ⟨m, hm, fun g k hgk => by rw [map_inv₀, map_inv₀, h g k hgk]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm, h⟩ := key hx hy
    exact ⟨m, hm, fun g k hgk => by rw [map_mul, map_mul, (h g k hgk).1, (h g k hgk).2]⟩

private theorem fd_frob {v : ℕ} [Fact v.Prime] {σ : GQ v}
    (hσ : UpperTheory.V.Loc.IsFrob (v := v) σ) {m : ℕ} (hm : ¬ v ∣ m)
    (j : ℕ) (y : Om v) (hy : y ^ m = 1) : (σ ^ j) y = y ^ v ^ j := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h1 : σ y = y ^ v := by
    have hn : ‖y‖ ^ m = 1 := by rw [← norm_pow, hy, norm_one]
    have hn' := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp hn
    exact KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hy, map_one])
      (fd_pow_root hy) (hσ y hn'.le)
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h1, ← pow_mul, pow_succ']

theorem UpperTheory.V.Loc.frobDense :
    ∀ {v : ℕ} [Fact v.Prime] (σ : GQ v), UpperTheory.V.Loc.IsFrob (v := v) σ →
      (Iq v ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ := by
  intro v _ σ hσ
  let H : ClosedSubgroup (GQ v) :=
    ⟨(Iq v ⊔ Subgroup.zpowers σ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  have hH := InfiniteGalois.fixingSubgroup_fixedField H
  have hle : Iq v ⊔ Subgroup.zpowers σ ≤ (H : Subgroup (GQ v)) := Subgroup.le_topologicalClosure _
  refine eq_top_iff.mpr fun g _ => ?_
  change g ∈ (H : Subgroup (GQ v))
  rw [← hH, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hxK : x ∈ MaximalUnramifiedExtension v := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v), IntermediateField.mem_fixedField_iff]
    exact fun f hf => hx f (hle (Subgroup.mem_sup_left hf))
  obtain ⟨m, hm, h⟩ := fd_level hxK
  obtain ⟨j, hj⟩ := KStar.IdealValuations.exists_pow_of_aut g hm
  rw [h g (σ ^ j) fun y hy => by rw [hj y hy, fd_frob hσ hm j y hy]]
  exact hx _ (hle (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers σ j)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
section
noncomputable section

namespace UpperTheory.V.Loc

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {Ω : Type} [Field Ω] [CharZero Ω] {v : ℕ} [Fact v.Prime]

def placeJ (j : Ω →+* Om v) : ValuationSubring Ω := (Valued.v : Valuation (Om v) NNReal).valuationSubring.comap j

variable [IsAlgClosure ℚ Ω]

def iota (j : Ω →+* Om v) : GQ v →* G ℚ Ω :=
  letI : Algebra Ω (Om v) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Om v) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Om v) Ω).comp
    { toFun := fun σ => σ.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem iota_spec (j : Ω →+* Om v) (σ : GQ v) (y : Ω) : j (iota j σ y) = σ (j y) := by
  letI : Algebra Ω (Om v) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Om v) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) Ω y

theorem exists_emb : Nonempty (Ω →+* Om v) := ⟨(IsAlgClosed.lift (R := ℚ) (S := Ω) (M := Om v)).toRingHom⟩

end UpperTheory.V.Loc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

variable {l : ℕ} [Fact l.Prime]

private theorem iqb_unit (x : integralClosure ℤ_[l] (PadicAlgCl l)) (h : ‖(x : PadicAlgCl l)‖ = 1) : IsUnit x := by
  have h0 : (x : PadicAlgCl l) ≠ 0 := by
    intro e; rw [e, norm_zero] at h; exact zero_ne_one h
  refine IsUnit.of_mul_eq_one ⟨(x : PadicAlgCl l)⁻¹, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ?_⟩
    (Subtype.ext (mul_inv_cancel₀ h0))
  rw [norm_inv, h, inv_one]

private theorem iqb_local : IsLocalRing (integralClosure ℤ_[l] (PadicAlgCl l)) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  have hx : ‖(x : PadicAlgCl l)‖ ≤ 1 := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 x.2
  rcases hx.eq_or_lt with h | h
  · exact Or.inl (iqb_unit x h)
  · refine Or.inr (iqb_unit _ ?_)
    have : ‖(1 : PadicAlgCl l)‖ ≠ ‖-(x : PadicAlgCl l)‖ := by rw [norm_one, norm_neg]; exact h.ne'
    have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this
    rw [norm_one, norm_neg, max_eq_left hx] at h2
    simpa [sub_eq_add_neg] using h2

private theorem iqb_frob : ∃ g : GQ l, IsFrob g := by
  haveI := iqb_local (l := l)
  have e : IsLocalRing.ResidueField ℤ_[l] ≃+* ZMod l := PadicInt.residueField
  obtain ⟨g, hg⟩ := GlobalTheory.exists_arithFrobenius_absGalois ℤ_[l] ℚ_[l] (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨y, hy, hm⟩ := hg ⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod] at hm
  have hle := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
    (y - (⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩ : integralClosure ℤ_[l] (PadicAlgCl l)) ^ l).2
  have hne := mt (iqb_unit _) hm
  have := lt_of_le_of_ne hle hne
  simpa [hy] using this

private theorem iqb_norm (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := KStar.IdealValuations.norm_aut_and_roots.1 g x

private theorem iqb_sub {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

private theorem iqb_mem (g : GQ l) : g ∈ Iq l ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1 := by
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact iqb_sub (by rwa [iqb_norm]) hlt
    · obtain ⟨m, ζ, hm, hζ, hxζ⟩ := KStar.IdealValuations.exists_root_congr heq
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
      have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
      have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
      rw [h2]
      exact iqb_sub (by rwa [iqb_norm]) hxζ
  · intro hg x hx
    have hle : MaximalUnramifiedExtension l ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      rw [MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
      rintro ζ ⟨m, hm0, hm, hζ⟩
      have hn : ‖ζ‖ = 1 := by
        have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').mp h1
      have h1 : g ζ = ζ := KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hζ, map_one]) hζ
        (hg ζ hn.le)
      have h2 : Subgroup.zpowers g ≤ MulAction.stabilizer (GQ l) ζ :=
        (Subgroup.zpowers_le (G := GQ l)).2 h1
      exact (IntermediateField.mem_fixedField_iff _ _).2 fun f hf => h2 hf
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) g (Subgroup.mem_zpowers g)

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.iqBasic :
    ∀ (v : ℕ) [Fact v.Prime], (Iq v).Normal ∧ IsClosed (Iq v : Set (GQ v)) ∧ (∀ g : GQ v, g ∈ Iq v ↔ ∀ x : Om v, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) ∧ (∃ σ : GQ v, IsFrob σ) ∧ ∀ σ σ' : GQ v, IsFrob σ → (IsFrob σ' ↔ σ⁻¹ * σ' ∈ Iq v) := by
  intro v _
  refine ⟨⟨fun n hn g => ?_⟩, ?_, iqb_mem, iqb_frob, fun σ σ' hσ => ?_⟩
  · rw [iqb_mem] at hn ⊢
    intro x hx
    have h := hn (g⁻¹ x) (by rwa [iqb_norm])
    have e : (g * n * g⁻¹) x - x = g (n (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹ x, mul_inv_cancel,
        AlgEquiv.one_apply]
    rwa [e, iqb_norm]
  · have : IsGalois ℚ_[v] (Om v) := {}
    exact InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension v)
  · have e : ∀ x : Om v, ‖(σ⁻¹ * σ') x - x‖ = ‖σ' x - σ x‖ := fun x => by
      rw [← iqb_norm σ, map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
    rw [iqb_mem]
    simp only [e]
    constructor
    · intro h x hx
      have h2 : σ' x - σ x = (σ' x - x ^ v) - (σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (hσ x hx)
    · intro h x hx
      have h2 : σ' x - x ^ v = (σ' x - σ x) - -(σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (by rw [norm_neg]; exact hσ x hx)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrField
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem finrank_key {Q E M V : Type} [Field Q] [Field E] [Algebra Q E] [FiniteDimensional Q E]
    [AddCommGroup M] [Module E M] [Module Q M] [IsScalarTower Q E M]
    [AddCommGroup V] [Module E V] [Module Q V] [IsScalarTower Q E V]
    (D : Submodule E M) (D' : Submodule Q M) (h : ∀ x, x ∈ D' ↔ x ∈ D) (n : ℕ) :
    finrank Q ↥D' = n * finrank Q V ↔ finrank E ↥D = n * finrank E V := by
  have e : D' = D.restrictScalars Q := by
    ext x
    exact h x
  have h1 : finrank Q ↥D' = finrank Q E * finrank E ↥D := by
    rw [Module.finrank_mul_finrank, e]
    rfl
  have h2 : finrank Q V = finrank Q E * finrank E V := (Module.finrank_mul_finrank Q E V).symm
  have hp : 0 < finrank Q E := Module.finrank_pos
  rw [h1, h2, mul_left_comm]
  exact Nat.mul_right_inj hp.ne'

theorem UpperTheory.V.Loc.isCrField :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E ↥(GK K) V), (Crys K ρ ↔ IsCrys ((PP l).PD K) ρ) ∧ (DeRham K ρ ↔ IsDR ((PP l).PD K) ρ) ∧ UpperTheory.V.Loc.finiteCocycles (GK K).subtype ρ = Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) ρ := by
  intro l _ K E _ _ _ V _ _ _ _ _ _ _ _ _ ρ
  have hB : ∀ g x, actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g x = actVB ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hD : ∀ g x, actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g x = actVdR ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hC : ∀ g x, actC (GK K).subtype ρ g x = actVB ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ g v ⊗ₜ[ℚ_[l]] (PP l).actQ (g : GQ l) b = ρ g v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB g b
      rw [(PP l).PD_actB]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨?_, ?_, ?_⟩
  · refine finrank_key (Formalism.WeaklyAdmissibleFiltrations.Dcris ((PP l).PD K) ρ) (Formalism.WeaklyAdmissibleFiltrations.Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun x => ?_) _
    simp only [Formalism.WeaklyAdmissibleFiltrations.Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hB]
  · refine finrank_key (Formalism.WeaklyAdmissibleFiltrations.DdR ((PP l).PD K) ρ) (Formalism.WeaklyAdmissibleFiltrations.DdR ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun x => ?_) _
    simp only [Formalism.WeaklyAdmissibleFiltrations.DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hD]
  · ext c
    change (c ∈ ReciprocityTheory.Gal.Z1 ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC (GK K).subtype ρ g x - x) ↔
      (c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actVB ((PP l).PD K) ρ g x - x)
    simp only [hC]
    exact Iff.rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemIK
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.memIK :
    ∀ {v : ℕ} [Fact v.Prime] (K : FinExt v) (g : ↥(GK K)), g ∈ IK K ↔ (g : GQ v) ∈ Iq v := by
  intro l _ K g
  refine ⟨fun hg => (Subgroup.closure_le ((MaximalUnramifiedExtension l).fixingSubgroup.comap (GK K).subtype)).2 (fun σ hσ => ?_) hg,
    fun hg => Subgroup.subset_closure (GlobalTheory.FrobGen.norm_sub_lt hg)⟩
  change (σ : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
  rintro x ⟨n, hn, hln, hx⟩
  have key : (σ : GQ l) x = x := GlobalTheory.Pst.eq_of_pow_eq_one_of_norm_sub_lt hln (by rw [← map_pow, hx, map_one]) hx
    (hσ x (GlobalTheory.Pst.norm_eq_one_of_pow_eq_one hn hx).le)
  rintro ⟨_, n, rfl⟩
  exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy _ (σ : GQ l) from key) n
end

