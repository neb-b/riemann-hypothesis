module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0009
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0002
public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsCounitEqOneMulEqZeroOfIsNilpotent
public import ReciprocityTheory.DualLattices.Bundle0017

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RaCpaf
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

lemma mem_pInt_iff [CharZero C] (hv : v.Integers R) (p : ℕ) [Fact p.Prime] (z : C) :
    z ∈ pInt (C := C) R p ↔ v z ≤ v (p : C) := by
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left zero_le (hv.map_le_one r)
  · intro h
    obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := z / p)
      (by rw [map_div₀]; exact div_le_one_of_le₀ h zero_le)
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ hp0]⟩

lemma pow_mem_order {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ A.carrier) (k : ℕ) :
    f ^ k ∈ A.carrier := by
  induction k with
  | zero => simpa using A.one_mem
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hf

lemma tl_mem_order (hv : v.Integers R) (p : ℕ) [Fact p.Prime] (hp : v (p : C) < 1)
    {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ A.carrier) :
    (fun x => tl p (f x)) ∈ A.carrier := by
  have : (fun x => tl p (f x)) =
      ∑ k ∈ Finset.Ico 1 p, fun x => (-1) ^ (k - 1) * (f x - 1) ^ k / (k : C) := by
    funext x; rw [Finset.sum_apply]; rfl
  rw [this]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
  obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := (-1) ^ (k - 1) / (k : C)) (by
    rw [map_div₀, val_nat_eq v p hp k h1 h2, map_pow, Valuation.map_neg, map_one, one_pow, div_one])
  have h3 := A.carrier.smul_mem r (pow_mem_order A (A.carrier.sub_mem hf A.one_mem) k)
  convert h3 using 1
  funext x
  simp only [Pi.smul_apply, Algebra.smul_def, Pi.pow_apply, Pi.sub_apply, Pi.one_apply, hr]
  ring

end

theorem cpaf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ μ : N →+ ZMod p, ∃ g ∈ afFun p AA.carrier, ∃ ε : R, v (algebraMap R C ε) ^ (p - 1) = v (p : C) ∧ g 0 = 0 ∧ ∀ x, g x - algebraMap R C ε * ((μ x).val : C) ∈ pInt (C := C) R p ∧ v (g x - algebraMap R C ε * ((μ x).val : C)) < v (algebraMap R C ε) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ AA μ
  have hpp : p.Prime := Fact.out
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hpp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  let ψ : AddChar N C := (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom μ
  have hψ : ∀ x, ψ x = ζ ^ (μ x).val := fun x => rfl
  have hψp : ∀ x, ψ x ^ p = 1 := fun x => by
    rw [hψ, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hζ1 := val_root v p hpp.ne_zero hζ.pow_eq_one
  have hε := val_tl_prim v p hp hζ
  obtain ⟨ε, hεe⟩ := hv.exists_of_le_one (r := tl p ζ) (hε.le.trans (val_prim_lt v p hp hζ).le)
  refine ⟨fun x => tl p (ψ x), ⟨tl_mem_order hv p hp AA (charmem p C v R hv hp N AA ψ), ?_⟩,
    ε, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · intro x y
    rw [mem_pInt_iff hv]
    simp only [AddChar.map_add_eq_mul]
    exact val_tl_add v p hp (hψp x) (hψp y)
  · rw [hεe, hε, val_prim v p hζ]
  · simp only [AddChar.map_zero_eq_one, tl_one]
  · rw [mem_pInt_iff hv, hεe]
    exact (val_tl_pow v p hp hζ1 _).trans (val_prim_pow_le v p hp hζ)
  · rw [hεe, hε]
    exact (val_tl_pow v p hp hζ1 _).trans_lt (val_prim_pow_lt v p hp hζ p hpp.one_lt)

lemma form_add {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] (p : ℕ) [Fact p.Prime]
    {ι : Type} [Fintype ι] (l : ι → R) (x y : ι → ZMod p) :
    algebraMap R C (∑ i, l i * (((x + y) i).val : R)) - algebraMap R C (∑ i, l i * ((x i).val : R))
      - algebraMap R C (∑ i, l i * ((y i).val : R)) ∈ pInt (C := C) R p := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h := Nat.mod_add_div ((x i).val + (y i).val) p
  rw [← ZMod.val_add] at h
  have h' := congrArg (Nat.cast : ℕ → C) h
  rw [pInt, Submodule.mem_span_singleton]
  refine ⟨-(l i * ((((x i).val + (y i).val) / p : ℕ) : R)), ?_⟩
  simp only [Algebra.smul_def, map_neg, map_mul, map_natCast, Pi.add_apply]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul] at h'
  linear_combination (-algebraMap R C (l i)) * h'

theorem lifts : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ (l : ι → R) (ε : R), ε • l ∈ afLat p AA.carrier → v (p : C) ≤ v (algebraMap R C ε) ^ (p - 1) → ∃ u : (ι → ZMod p) → C, (fun x => algebraMap R C ε * u x) ∈ afFun p AA.carrier ∧ (∀ x, v (u x) ≤ 1) ∧ ∀ x, v (u x - algebraMap R C (∑ i, l i * ((x i).val : R))) < 1 := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA l ε hl hε
  have hpp : p.Prime := Fact.out
  have hp1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
  have hp0 : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hpp.ne_zero)
  have hε0 : v (algebraMap R C ε) ≠ 0 := by
    intro h
    rw [h, zero_pow hp1] at hε
    exact hp0 (le_antisymm hε zero_le)
  have hε0' : algebraMap R C ε ≠ 0 := (Valuation.ne_zero_iff v).1 hε0
  suffices h : ∃ u : (ι → ZMod p) → C, (fun x => algebraMap R C ε * u x) ∈ afFun p AA.carrier ∧
      ∀ x, v (u x - algebraMap R C (∑ i, l i * ((x i).val : R))) < 1 by
    obtain ⟨u, h1, h2⟩ := h
    refine ⟨u, h1, fun x => ?_, h2⟩
    rw [← sub_add_cancel (u x) (algebraMap R C (∑ i, l i * ((x i).val : R)))]
    exact v.map_add_le (h2 x).le (hv.map_le_one _)
  rcases lt_or_ge (v (p : C)) (v (algebraMap R C ε)) with hlt | hge
  · obtain ⟨g, hg, h⟩ := hl
    refine ⟨fun x => g x / algebraMap R C ε, ?_, fun x => ?_⟩
    · simp only [mul_div_cancel₀ _ hε0']
      refine ⟨hg, fun x y => ?_⟩
      have := Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (h (x + y)) (h x)) (h y))
        (form_add (C := C) p (ε • l) x y)
      convert this using 1
      ring
    · have h1 := (mem_pInt_iff hv p _).1 (h x)
      have h2 : g x / algebraMap R C ε - algebraMap R C (∑ i, l i * ((x i).val : R)) =
          (g x - algebraMap R C (∑ i, (ε • l) i * ((x i).val : R))) / algebraMap R C ε := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, map_mul]
        field_simp
      rw [h2, map_div₀, div_lt_one₀ (pos_iff_ne_zero.2 hε0)]
      exact h1.trans_lt hlt
  · have hc := fun i => cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)
    choose g hg e he _ hge' using hc
    have hee : ∀ i, v (algebraMap R C ε) ≤ v (algebraMap R C (e i)) := by
      intro i
      refine hge.trans ?_
      rw [← he i]
      exact pow_le_of_le_one zero_le (hv.map_le_one _) hp1
    have he0 : ∀ i, v (algebraMap R C (e i)) ≠ 0 := fun i h =>
      hε0 (le_antisymm (h ▸ hee i) zero_le)
    have he0' : ∀ i, algebraMap R C (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff v).1 (he0 i)
    choose r hr using fun i => hv.dvd_of_le (hee i)
    refine ⟨fun x => ∑ i, algebraMap R C (l i) * (g i x / algebraMap R C (e i)), ?_, fun x => ?_⟩
    · have := Submodule.sum_mem (afFun p AA.carrier) (t := Finset.univ)
        fun i _ => Submodule.smul_mem _ (l i * r i) (hg i)
      convert this using 1
      funext x
      rw [Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h0 := he0' i
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      conv_lhs => rw [hr i, map_mul]
      field_simp
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine v.map_sum_lt one_ne_zero fun i _ => ?_
      have h0 := he0' i
      have h2 : algebraMap R C (l i) * (g i x / algebraMap R C (e i)) -
          algebraMap R C (l i * ((x i).val : R)) = algebraMap R C (l i) *
          ((g i x - algebraMap R C (e i) * ((x i).val : C)) / algebraMap R C (e i)) := by
        rw [map_mul, map_natCast]
        field_simp
      rw [h2, map_mul, map_div₀]
      refine mul_lt_one_of_nonneg_of_lt_one_right (hv.map_le_one _) zero_le ?_
      rw [div_lt_one₀ (pos_iff_ne_zero.2 (he0 i))]
      exact (hge' i x).2

end PositivityTheory.HtPt.Ra
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RfHopf
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
open scoped TensorProduct

namespace PositivityTheory.HtPt.Rf

theorem exists_pt_of_gen {C R A : Type} [Field C] [CommRing R] [IsDomain R] [Algebra R C]
    [IsFractionRing R C] [IsIntegrallyClosed R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] R, ∀ a, algebraMap R C (ψ a) = φ a := by
  have h : ∀ a : A, ∃ r : R, algebraMap R C r = φ a := fun a =>
    IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := R) a).map φ)
  choose f hf using h
  have inj := IsFractionRing.injective R C
  let ψ : A →ₐ[R] R :=
    { toFun := f,
      map_one' := inj (by rw [hf, map_one, map_one]),
      map_mul' := fun a b => inj (by rw [hf, map_mul, map_mul, hf, hf]),
      map_zero' := inj (by rw [hf, map_zero, map_zero]),
      map_add' := fun a b => inj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]),
      commutes' := fun r => inj (by rw [hf, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]) }
  exact ⟨ψ, fun a => hf a⟩

noncomputable def evGen (C : Type) {R A : Type} [Field C] [CommRing R] [Algebra R C]
    [CommRing A] [Algebra R A] {N : Type} (pt : N → (A →ₐ[R] R)) : C ⊗[R] A →ₐ[C] (N → C) :=
  AlgHom.pi fun x => Algebra.TensorProduct.lift (AlgHom.id C C) ((Algebra.ofId R C).comp (pt x))
    fun _ _ => Commute.all _ _

theorem evGen_tmul (C : Type) {R A : Type} [Field C] [CommRing R] [Algebra R C]
    [CommRing A] [Algebra R A] {N : Type} (pt : N → (A →ₐ[R] R)) (c : C) (a : A) (x : N) :
    evGen C pt (c ⊗ₜ a) x = c * algebraMap R C (pt x a) := by
  simp [evGen, Algebra.ofId_apply]

theorem evGen_bij {C R A : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing R] [IsDomain R]
    [Algebra R C] [IsFractionRing R C] [IsIntegrallyClosed R] [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] {N : Type} [Fintype N] (pt : N → (A →ₐ[R] R)) (hpt : Function.Bijective pt) :
    Function.Bijective (evGen C pt) := by
  classical
  have inj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  have key : ∀ χ : C ⊗[R] A →ₐ[C] C, ∃ x, ∀ b, χ b = evGen C pt b x := by
    intro χ
    obtain ⟨ψ, hψ⟩ := exists_pt_of_gen ((χ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    obtain ⟨x, rfl⟩ := hpt.2 ψ
    refine ⟨x, fun b => ?_⟩
    have h : χ = (Pi.evalAlgHom C (fun _ : N => C) x).comp (evGen C pt) := by
      apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      ext a
      show χ (1 ⊗ₜ a) = evGen C pt (1 ⊗ₜ a) x
      rw [evGen_tmul, one_mul]
      exact (hψ a).symm
    rw [h]
    rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    haveI : IsReduced (C ⊗[R] A) := GlobalTheory.isReduced_of_hopfAlgebra_of_isAlgClosed C _
    haveI : IsArtinianRing (C ⊗[R] A) := IsArtinianRing.of_finite C _
    apply (IsArtinianRing.equivPi (C ⊗[R] A)).injective
    rw [map_zero]
    funext m
    rw [IsArtinianRing.equivPi_apply]
    haveI := m.isMaximal
    letI : Field ((C ⊗[R] A) ⧸ m.asIdeal) := Ideal.Quotient.field _
    have bij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C) (K := (C ⊗[R] A) ⧸ m.asIdeal)
    let e := AlgEquiv.ofBijective (Algebra.ofId C ((C ⊗[R] A) ⧸ m.asIdeal)) bij
    obtain ⟨x, hx⟩ := key (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m.asIdeal))
    have h1 := hx b
    rw [hb] at h1
    have h2 : e.symm (Ideal.Quotient.mk m.asIdeal b) = 0 := h1
    have h3 := congrArg e h2
    rw [AlgEquiv.apply_symm_apply, map_zero] at h3
    exact h3
  · by_contra hns
    have hlt : LinearMap.range (evGen C pt).toLinearMap < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hns
      exact LinearMap.range_eq_top.1 h
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    have hfE : ∀ b, f (evGen C pt b) = 0 := fun b => by
      have h : f (evGen C pt b) ∈ (LinearMap.range (evGen C pt).toLinearMap).map f := ⟨evGen C pt b, ⟨b, rfl⟩, rfl⟩
      rw [hf] at h
      exact (Submodule.mem_bot C).1 h
    let M : N → (C ⊗[R] A →* C) := fun x => ((Pi.evalAlgHom C (fun _ : N => C) x).comp (evGen C pt)).toRingHom.toMonoidHom
    have hM : ∀ x b, M x b = evGen C pt b x := fun _ _ => rfl
    have hMinj : Function.Injective M := by
      intro x y hxy
      apply hpt.1
      ext a
      apply inj
      have h := congrArg (fun g : C ⊗[R] A →* C => g (1 ⊗ₜ a)) hxy
      simp only [hM, evGen_tmul, one_mul] at h
      exact h
    have hli := (linearIndependent_monoidHom (C ⊗[R] A) C).comp M hMinj
    have hsingle : ∀ (x : N) (c : C), (Pi.single x c : N → C) = c • Pi.single x 1 := by
      intro x c
      ext j
      by_cases h : j = x
      · subst h; simp
      · simp [Pi.single_apply, h]
    have hc := Fintype.linearIndependent_iff.1 hli (fun x => f (Pi.single x 1)) (by
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply, hM]
      rw [← hfE b]
      conv_rhs => rw [← Finset.univ_sum_single (evGen C pt b)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsingle x (evGen C pt b x), map_smul, smul_eq_mul, mul_comm])
    apply hf0
    apply LinearMap.pi_ext
    intro x c
    rw [hsingle x c, map_smul, hc x, smul_zero]
    rfl

theorem hopfalg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Free R A], ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ pt : N → (A →ₐ[R] R), Function.Bijective pt → (∀ x y a, pt (x + y) a = Algebra.TensorProduct.lift (pt x) (pt y) (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := R) a)) → (∀ a : A, (∀ x, pt x a = 0) → a = 0) ∧ Fintype.card N = Module.finrank R A ∧ ∃ AA : HopfOrder (C := C) R N, ∀ g, g ∈ AA.carrier ↔ ∃ a : A, g = fun x => algebraMap R C (pt x a) := by
  intro p _ C _ _ _ v R _ _ hv hp A _ _ _ _ _ N _ _ _ pt hbij hadd
  classical
  haveI : IsDomain R := hv.hom_inj.isDomain
  haveI : IsFractionRing R C := hv.isFractionRing
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  have hB := evGen_bij (C := C) pt hbij
  have hinjA : Function.Injective (fun a : A => (1 : C) ⊗ₜ[R] a) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R C) hv.hom_inj
    intro a b hab
    apply (TensorProduct.lid R A).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hab
  have sep : ∀ a : A, (∀ x, pt x a = 0) → a = 0 := by
    intro a ha
    apply hinjA
    apply hB.1
    funext x
    simp only [evGen_tmul, ha x, map_zero, mul_zero, TensorProduct.tmul_zero, Pi.zero_apply]
  have card : Fintype.card N = Module.finrank R A := by
    have h1 := (LinearEquiv.ofBijective (evGen C pt).toLinearMap hB).finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_baseChange] at h1
    exact h1.symm
  have hP : ∀ x y, WithConv.toConv (pt (x + y)) = WithConv.toConv (pt x) * WithConv.toConv (pt y) := by
    intro x y
    apply WithConv.ofConv_injective
    ext a
    rw [hadd, AlgHom.convMul_apply]
  have h0 : WithConv.toConv (pt 0) = (1 : WithConv (A →ₐ[R] R)) := by
    have h := hP 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := WithConv.toConv (pt 0)) (by rw [mul_one, ← h])
  have hS : ∀ x a, pt (-x) a = pt x (HopfAlgebra.antipode R a) := by
    intro x a
    have hn : WithConv.toConv (pt (-x)) = (WithConv.toConv (pt x))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hP, neg_add_cancel, h0]
    have h := congrArg (fun f : WithConv (A →ₐ[R] R) => (WithConv.ofConv f) a) hn
    exact h
  let E : A →ₗ[R] (N → C) := LinearMap.pi (fun x => (Algebra.linearMap R C).comp (pt x).toLinearMap)
  have hE : ∀ a x, E a x = algebraMap R C (pt x a) := fun _ _ => rfl
  refine ⟨sep, card, ⟨{ carrier := LinearMap.range E, lat := ?_, le_int := ?_, one_mem := ?_, mul_mem := ?_, comul := ?_, antipode := ?_ }, ?_⟩⟩
  · have hc : Fintype.card N = Fintype.card (Module.Free.ChooseBasisIndex R A) := by
      rw [card, Module.finrank_eq_card_chooseBasisIndex]
    let b : Module.Basis N R A := (Module.Free.chooseBasis R A).reindex (Fintype.equivOfCardEq hc).symm
    let bc : Module.Basis N C (C ⊗[R] A) := Algebra.TensorProduct.basis C b
    let le := LinearEquiv.ofBijective (evGen C pt).toLinearMap hB
    refine ⟨LinearMap.toMatrix bc (Pi.basisFun C N) le, LinearEquiv.isUnit_det le bc (Pi.basisFun C N), ?_⟩
    have hcol : (fun j x => LinearMap.toMatrix bc (Pi.basisFun C N) le x j) = E ∘ b := by
      funext j x
      rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
      show evGen C pt (bc j) x = _
      rw [Algebra.TensorProduct.basis_apply, evGen_tmul, one_mul]
      rfl
    rw [hcol, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  · rintro g ⟨a, rfl⟩ x
    exact ⟨pt x a, rfl⟩
  · refine ⟨1, ?_⟩
    funext x
    simp [hE]
  · rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    funext x
    simp [hE]
  · rintro f ⟨a, rfl⟩
    have gen : ∀ t : A ⊗[R] A, (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) t)) ∈ tensorSpan R (LinearMap.range E) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero =>
        have h : (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) (0 : A ⊗[R] A))) = 0 := by
          funext q
          simp
        rw [h]
        exact zero_mem _
      | tmul a b =>
        apply Submodule.subset_span
        refine ⟨E a, ⟨a, rfl⟩, E b, ⟨b, rfl⟩, ?_⟩
        funext q
        simp [hE]
      | add s t hs ht =>
        have h : (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) (s + t))) = (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) s)) + (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) t)) := by
          funext q
          simp
        rw [h]
        exact add_mem hs ht
    have h := gen (Coalgebra.comul a)
    convert h using 1
    funext q
    show E a (q.1 + q.2) = _
    rw [hE, hadd]
  · rintro f ⟨a, rfl⟩
    refine ⟨HopfAlgebra.antipode R a, ?_⟩
    funext x
    rw [hE, hE, hS]
  · intro g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩

end PositivityTheory.HtPt.Rf
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RiEasy
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ri

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

lemma mem_pInt (p : ℕ) (z : C) : z ∈ pInt (C := C) R p ↔ ∃ r : R, algebraMap R C (r * p) = z := by
  unfold GlobalTheory.CompanionTheory.Ar.GR.pInt
  rw [Submodule.mem_span_singleton]
  simp only [Algebra.smul_def, map_mul, map_natCast]

lemma alg_mem_pInt (p : ℕ) {r : R} (h : r ∈ Ideal.span {(p : R)}) :
    algebraMap R C r ∈ pInt (C := C) R p := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 h
  exact (PositivityTheory.HtPt.Ri.mem_pInt p _).2 ⟨a, rfl⟩

lemma add_zero_mem {p : ℕ} {N : Type} [AddCommGroup N] {g : N → C}
    (hg : g ∈ addFun (C := C) R p N) : g 0 ∈ pInt (C := C) R p := by
  have h := (show ∀ x y : N, g (x + y) - g x - g y ∈ GlobalTheory.CompanionTheory.Ar.GR.pInt (C := C) R p
    from hg) 0 0
  rw [add_zero, sub_self, zero_sub] at h
  simpa using Submodule.neg_mem _ h

lemma add_nsmul_mem {p : ℕ} {N : Type} [AddCommGroup N] {g : N → C}
    (hg : g ∈ addFun (C := C) R p N) (y : N) (n : ℕ) :
    g (n • y) - n * g y ∈ pInt (C := C) R p := by
  induction n with
  | zero => simpa using PositivityTheory.HtPt.Ri.add_zero_mem hg
  | succ n ih =>
    have h := (show ∀ x y : N, g (x + y) - g x - g y ∈ GlobalTheory.CompanionTheory.Ar.GR.pInt (C := C) R p
      from hg) (n • y) y
    have hsum := Submodule.add_mem _ h ih
    rw [succ_nsmul]
    convert hsum using 1
    push_cast
    ring

lemma val_add_mem (p : ℕ) [NeZero p] (a b : ZMod p) :
    (((a + b).val : R) - (a.val : R) - (b.val : R)) ∈ Ideal.span {(p : R)} := by
  rw [Ideal.mem_span_singleton']
  refine ⟨-(((a.val + b.val) / p : ℕ) : R), ?_⟩
  have h := Nat.mod_add_div (a.val + b.val) p
  have h' : (((a.val + b.val) % p : ℕ) : R) + (p : R) * (((a.val + b.val) / p : ℕ) : R)
      = (a.val : R) + b.val := by
    rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, h]
  rw [ZMod.val_add]
  linear_combination -h'

end

theorem card_addChar (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N : Type)
    [AddCommGroup N] [Fintype N] : Nat.card (AddChar N C) = Fintype.card N := by
  have hne : Monoid.exponent (Multiplicative N) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : NeZero (Monoid.exponent (Multiplicative N)) := ⟨hne⟩
  haveI : NeZero (Monoid.exponent (Multiplicative N) : C) := ⟨Nat.cast_ne_zero.2 hne⟩
  rw [Nat.card_congr (AddChar.toMonoidHomEquiv.trans MonoidHom.toHomUnitsMulEquiv.toEquiv),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card]

end PositivityTheory.HtPt.Ri
end
end

