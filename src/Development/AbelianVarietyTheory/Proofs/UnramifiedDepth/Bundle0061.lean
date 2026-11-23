module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SquarefreeMapMinpolyInt
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotent
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_eps {C B OE : Type} [Field C] [CommRing B] [Algebra C B] [CommRing OE]
    (σ : B →ₐ[C] C) (j : OE →+* B) (hj : Submodule.span C (Set.range j) = ⊤)
    (hsup : (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) = ⊤) :
    ∃ ε : B, σ ε = 1 ∧ ∀ z, z * ε = σ z • ε := by
  have key : ∀ z : B, ∃ ε : B, σ ε = σ z ∧ ∀ a, j a * ε = σ (j a) • ε := by
    intro z
    have hz : z ∈ (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) := by
      rw [hsup]; trivial
    induction hz using Submodule.iSup_induction' with
    | mem τ x hx =>
      have hx' : ∀ a, j a * x = τ a • x := fun a => by
        have := (Submodule.mem_iInf _).1 hx a
        rw [Module.End.mem_eigenspace_iff] at this
        exact this
      by_cases h0 : σ x = 0
      · exact ⟨0, by simp [h0], by simp⟩
      · refine ⟨x, rfl, fun a => ?_⟩
        have h1 := congrArg σ (hx' a)
        rw [map_mul, map_smul, smul_eq_mul] at h1
        rw [hx' a, mul_right_cancel₀ h0 h1]
    | zero => exact ⟨0, rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, by simp [ha, hb], fun c => by rw [mul_add, smul_add, ha', hb']⟩
  obtain ⟨ε, h1, h2⟩ := key 1
  refine ⟨ε, by simpa using h1, fun z => ?_⟩
  have hz : z ∈ Submodule.span C (Set.range j) := by rw [hj]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h2 a
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, hx, hy, map_add (f := _), add_smul]
  | smul c x _ hx => rw [smul_mul_assoc, hx, map_smul, smul_eq_mul, mul_smul]

private theorem core {C B OE κ I H : Type} [Field C] [CommRing B] [Algebra C B] [CommRing OE]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Fintype H]
    (σ : B →ₐ[C] C) (j : OE →+* B) (hj : Submodule.span C (Set.range j) = ⊤)
    (hsup : (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) = ⊤)
    (ρ : B →ₐ[C] Matrix κ κ C) (e : B) (he : σ e = 1) (b : I → B)
    (hb : ∀ z, z * e ∈ Submodule.span C (Set.range b)) (y : H → κ → C)
    (hli : LinearIndependent C (fun q : I × H => ρ (b q.1) *ᵥ y q.2))
    (hsp : ∀ x, ρ e *ᵥ x ∈ Submodule.span C (Set.range fun q : I × H => ρ (b q.1) *ᵥ y q.2)) :
    Module.finrank C ↥(⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) =
      Fintype.card H := by
  obtain ⟨ε, h1, h2⟩ := exists_eps σ j hj hsup
  have hεe : ε * e = ε := by rw [mul_comm, h2, he, one_smul]
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 (hb ε)
  rw [hεe] at ht
  have hmul : ∀ (z : B) (x : κ → C), ρ z *ᵥ (ρ ε *ᵥ x) = σ z • (ρ ε *ᵥ x) := fun z x => by
    rw [Matrix.mulVec_mulVec, ← map_mul, h2, map_smul, Matrix.smul_mulVec]
  have hmul' : ∀ (z : B) (x : κ → C), ρ ε *ᵥ (ρ z *ᵥ x) = σ z • (ρ ε *ᵥ x) := fun z x => by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm, h2, map_smul, Matrix.smul_mulVec]
  have hli' : LinearIndependent C (fun l : H => ρ ε *ᵥ y l) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc l
    have h3 := hli (fun q => c q.2 * t q.1) (by
      rw [← hc, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun l _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← ht, map_sum, Matrix.sum_mulVec, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Matrix.smul_mulVec, mul_smul])
    by_contra hl
    have h4 : ∀ i, t i = 0 := fun i => (mul_eq_zero.1 (h3 (i, l))).resolve_left hl
    have h5 : ε = 0 := by rw [← ht]; simp [h4]
    rw [h5, map_zero] at h1
    exact zero_ne_one h1
  have hE : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) =
      Submodule.span C (Set.range fun l : H => ρ ε *ᵥ y l) := by
    apply le_antisymm
    · intro x hx
      have hx' : ∀ a, ρ (j a) *ᵥ x = σ (j a) • x := fun a => by
        have := (Submodule.mem_iInf _).1 hx a
        rw [Module.End.mem_eigenspace_iff] at this
        simpa using this
      have hx2 : ∀ z, ρ z *ᵥ x = σ z • x := fun z => by
        have hz : z ∈ Submodule.span C (Set.range j) := by rw [hj]; trivial
        induction hz using Submodule.span_induction with
        | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hx' a
        | zero => simp
        | add x y _ _ hx hy => rw [map_add (f := _), Matrix.add_mulVec, hx, hy, map_add (f := _), add_smul]
        | smul c x _ hx => rw [map_smul, Matrix.smul_mulVec, hx, map_smul, smul_eq_mul, mul_smul]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 (hsp x)
      have : x = ρ ε *ᵥ (ρ e *ᵥ x) := by rw [hx2 e, he, one_smul, hx2, h1, one_smul]
      rw [this, ← hc, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      rw [Matrix.mulVec_smul, hmul']
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine (Submodule.mem_iInf _).2 fun a => ?_
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hmul _ _
  rw [hE, finrank_span_eq_card hli']

theorem eigDim_eq_of_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]) (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) → Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) → ∀ τ ∈ Emb (O := O) w.e, eigDim C (fun a : OE => (ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) ((algebraMap O C).comp τ) = h := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ _ _ _ w b κ _ _ ρ h y hli hsp τ hτ
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra
  haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap ℤ_[p] C) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h1 | h1
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero h1
    · exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) (pow_eq_zero_iff'.1 h1).1
  haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let σ : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] C := Algebra.TensorProduct.lift (AlgHom.id C C)
    ((IsScalarTower.toAlgHom ℤ_[p] O C).comp (tauExt τ)) (fun _ _ => Commute.all _ _)
  let ρB : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] Matrix κ κ C :=
    Algebra.TensorProduct.lift (Algebra.ofId C (Matrix κ κ C))
    ((Algebra.ofId ℤ_[p] C).mapMatrix.comp ρ) (fun _ _ => Algebra.commutes _ _)
  let j : OE →+* (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) :=
    (Algebra.TensorProduct.includeRight (R := ℤ_[p]) (A := C) (B := ℤ_[p] ⊗[ℤ] OE)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  have hj : ∀ a, j a = 1 ⊗ₜ (1 ⊗ₜ a) := fun a => rfl
  have hσ : ∀ a, σ (1 ⊗ₜ a) = algebraMap O C (tauExt τ a) := fun a => by simp [σ]
  have hρ : ∀ a, ρB (1 ⊗ₜ a) = (ρ a).map (algebraMap ℤ_[p] C) := fun a => by
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, _root_.one_mul]
    rfl
  have hmv : ∀ a x, ρB (1 ⊗ₜ a) *ᵥ (algebraMap ℤ_[p] C ∘ x) = algebraMap ℤ_[p] C ∘ (ρ a *ᵥ x) := by
    intro a x
    funext i
    rw [hρ]
    exact (RingHom.map_mulVec _ _ _ _).symm
  have hs : ∀ (c : C) (r : ℤ_[p]) (a : ℤ_[p] ⊗[ℤ] OE),
      (c ⊗ₜ[ℤ_[p]] (r • a)) = (r • c) • ((1 : C) ⊗ₜ[ℤ_[p]] a) := fun c r a => by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have H := core (I := Fin w.n) (H := Fin h) σ j ?_ ((GlobalTheory.order_rep_diagonalisable C OE).2 _ _).2 ρB (1 ⊗ₜ w.e)
    (by rw [hσ, show tauExt τ w.e = 1 from hτ, map_one])
    (fun i => 1 ⊗ₜ (b i : ℤ_[p] ⊗[ℤ] OE)) ?_ (fun l => algebraMap ℤ_[p] C ∘ y l) ?_ ?_
  · rw [Fintype.card_fin] at H
    have h1 : ∀ a, ρB (j a) = ((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C) := by
      intro a
      rw [hj, hρ, Matrix.map_map]
      rfl
    have h2 : ∀ a, σ (j a) = ((algebraMap O C).comp τ) a := by
      intro a
      rw [hj, hσ]
      simp [tauExt]
    have h3 : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρB (j a))) (σ (j a))) = ⨅ a : OE,
        Module.End.eigenspace (Matrix.toLin' (((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C)))
          (((algebraMap O C).comp τ) a) := iInf_congr fun a => by rw [h1, h2]
    rw [h3] at H
    exact H
  · rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul c a =>
      induction a using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
      | tmul r a =>
        have : r ⊗ₜ[ℤ] a = r • ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, hs]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | tmul c a =>
      have h1 := congrArg Subtype.val (b.sum_repr ⟨w.e * a, a, rfl⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, mul_comm a, ← h1, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · simp only [hmv]
    exact linearIndependent_algebraMap_comp_iff.2 hli
  · intro x
    simp only [hmv]
    rw [← Finset.univ_sum_single x, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h1 : (Pi.single k (x k) : κ → C) = x k • (algebraMap ℤ_[p] C ∘ (Pi.single k 1 : κ → ℤ_[p])) := by
      funext i
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    rw [h1, Matrix.mulVec_smul, hmv]
    refine Submodule.smul_mem _ _ ?_
    have h2 : ρ w.e *ᵥ (Pi.single k 1 : κ → ℤ_[p]) ∈ LinearMap.range (Matrix.mulVecLin (ρ w.e)) := ⟨_, rfl⟩
    rw [← hsp] at h2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun q => algebraMap ℤ_[p] C (c q), ?_⟩
    rw [← hc]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowExponentPartMemGaugedCurveLogarithms
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowLaw.TypPart

variable {C : Type} [Field C]

theorem ge_intCast (V : VF C) (a : ℤ) : V.Ge 0 (a : C) := by
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · simpa using VF.ge_natCast (V := V) n
  · simpa using (VF.ge_natCast (V := V) n).neg

theorem v_prime_eq_zero (V : VF C) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l) : V.v (p : C) = 0 := by
  have hc : IsCoprime (p : ℤ) (V.l : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp V.l_prime).2 hpl)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : C) * (p : C) + (b : C) * (V.l : C) = 1 := by
    have := congrArg (fun z : ℤ => (z : C)) hab
    simpa using this
  have h0 : (0 : WithTop ℝ) ≤ V.v (p : C) := by simpa [VF.Ge] using VF.ge_natCast (V := V) p
  have ha : (0 : WithTop ℝ) ≤ V.v (a : C) := by simpa [VF.Ge] using ge_intCast V a
  have hb : (0 : WithTop ℝ) ≤ V.v (b : C) := by simpa [VF.Ge] using ge_intCast V b
  by_contra hne
  have hpos : (0 : WithTop ℝ) < V.v (p : C) := lt_of_le_of_ne h0 (Ne.symm hne)
  have e1 : (0 : WithTop ℝ) < V.v ((a : C) * (p : C)) := by
    rw [V.v.map_mul]; exact lt_of_lt_of_le hpos (le_add_of_nonneg_left ha)
  have e2 : (0 : WithTop ℝ) < V.v ((b : C) * (V.l : C)) := by
    rw [V.v.map_mul, V.v_l]; exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hb)
  have := V.v.map_lt_add e1 e2
  rw [h1, V.v.map_one] at this
  exact lt_irrefl _ this

theorem ge_of_pow_eq_one (V : VF C) {ζ : C} {p : ℕ} (hp : 0 < p) (h : ζ ^ p = 1) : V.Ge 0 ζ := by
  have h1 : p • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv, ← WithTop.coe_nsmul] at h1
    have h2 : p • t = 0 := by exact_mod_cast h1
    have h3 : t = 0 := by
      rw [nsmul_eq_mul] at h2
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd (by exact_mod_cast h) hp.ne'
      · exact h
    rw [h3]

theorem sum_pow_root {ζ : C} {p : ℕ} (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∑ j ∈ Finset.range p, (ζ ^ j) ^ m = if p ∣ m then (p : C) else 0 := by
  have e : ∀ j, (ζ ^ j) ^ m = (ζ ^ m) ^ j := fun j => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [e]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]; simp
  · have hne : ζ ^ m - 1 ≠ 0 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 (sub_eq_zero.1 h'))
    have := geom_sum_mul (ζ ^ m) p
    rw [← pow_mul, mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne


open Classical in
def filt (P : ℕ → Prop) (f : PowerSeries C) : PowerSeries C :=
  PowerSeries.mk fun m => if P m then PowerSeries.coeff m f else 0

open Classical in
theorem coeff_filt (P : ℕ → Prop) (f : PowerSeries C) (m : ℕ) :
    PowerSeries.coeff m (filt P f) = if P m then PowerSeries.coeff m f else 0 := by
  simp [filt]

theorem sub_avg [CharZero C] {ζ : C} {p : ℕ} (hp : 0 < p) (hζ : IsPrimitiveRoot ζ p) (f : PowerSeries C) :
    f + -((p : C)⁻¹ • ∑ j ∈ Finset.range p, PowerSeries.rescale (ζ ^ j) f) = filt (fun m => ¬ p ∣ m) f := by
  ext m
  have hp' : (p : C) ≠ 0 := by exact_mod_cast hp.ne'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_filt, map_add (f := _), map_neg, PowerSeries.coeff_smul, map_sum]
  simp_rw [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_pow_root hζ]
  by_cases h : p ∣ m
  · simp [h, hp']
  · simp [h]

theorem filt_filt (P Q : ℕ → Prop) (f : PowerSeries C) :
    filt P (filt Q f) = filt (fun m => P m ∧ Q m) f := by
  ext m
  rw [coeff_filt, coeff_filt, coeff_filt]
  by_cases h : P m <;> by_cases h' : Q m <;> simp [h, h']

theorem filt_congr {P Q : ℕ → Prop} (h : ∀ m, P m ↔ Q m) (f : PowerSeries C) : filt P f = filt Q f := by
  have : P = Q := funext fun m => propext (h m)
  rw [this]

theorem filt_true {P : ℕ → Prop} (h : ∀ m, P m) (f : PowerSeries C) : filt P f = f := by
  ext m
  rw [coeff_filt, if_pos (h m)]

def Good (l n m : ℕ) : Prop := ∀ p < n, p.Prime → p ≠ l → ¬ p ∣ m

theorem coeff_filt_good {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (f : PowerSeries C) (m n : ℕ) (hn : m + 3 ≤ n) :
    PowerSeries.coeff m (filt (Good l n) f) = PowerSeries.coeff m (typ l f) := by
  rw [coeff_filt]
  unfold typ
  by_cases hm : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := hm
    rw [coeff_tyS_pow hl.two_le, if_pos]
    intro p _ hp hpl hd
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow hd))
  · rw [coeff_tyS_of_ne _ m (fun s hs => hm ⟨s, hs⟩), if_neg]
    intro hg
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact hg 2 (by omega) Nat.prime_two (Ne.symm hl2) (dvd_zero 2)
    · apply hm
      refine ⟨_, (Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_).symm⟩
      intro q hq hqm
      by_contra hne
      exact hg q (by have := Nat.le_of_dvd hpos hqm; omega) hq hne hqm

variable {V : VF C} {d : ℕ} [NeZero d] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

theorem filt_not_dvd_mem (hX : RLaw X V) (g : Fin 2) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l)
    (a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) (ha : a ∈ Cv X V g) :
    ((fun i => filt (fun m => ¬ p ∣ m) (a.1 i), fun q => filt (fun m => ¬ p ∣ m) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
  have := hX.charZero
  have := hX.closed
  have : NeZero (p : C) := ⟨by exact_mod_cast hp.ne_zero⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  obtain ⟨h0, hadd, hneg, hres⟩ := _root_.GlobalTheory.RowLaw.cv_group C V d I κ X hX g
  have hζ0 : V.Ge 0 ζ := ge_of_pow_eq_one V hp.pos hζ.pow_eq_one
  have hs : ∀ n : ℕ, ((fun i => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.1 i),
      fun q => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact h0
    | succ n ih =>
      have := hadd _ ih _ (hres (ζ ^ n) (hζ0.pow n) a ha)
      simp only [Finset.sum_range_succ]
      exact this
  have h2 := hadd _ ha _ (hneg _ (_root_.GlobalTheory.RowLaw.cv_inv_natCast_smul_mem C V d I κ X hX g p (v_prime_eq_zero V hp hpl) _ (hs p)))
  convert h2 using 1
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · exact (sub_avg hp.pos hζ (a.1 i)).symm
  · exact (sub_avg hp.pos hζ (a.2 q)).symm

theorem filt_good_mem (hX : RLaw X V) (g : Fin 2)
    (a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) (ha : a ∈ Cv X V g) (n : ℕ) :
    ((fun i => filt (Good V.l n) (a.1 i), fun q => filt (Good V.l n) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
  induction n with
  | zero =>
    have h : ∀ m, Good V.l 0 m := fun m p hp => absurd hp (Nat.not_lt_zero p)
    simp only [filt_true h]
    exact ha
  | succ n ih =>
    by_cases hn : n.Prime ∧ n ≠ V.l
    · have h : ∀ m, Good V.l (n + 1) m ↔ (¬ n ∣ m ∧ Good V.l n m) := by
        intro m
        constructor
        · intro hg
          exact ⟨hg n (by omega) hn.1 hn.2, fun p hp => hg p (by omega)⟩
        · rintro ⟨h1, h2⟩ p hp hpp hpl
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
          · exact h2 p h hpp hpl
          · exact h1
      have := filt_not_dvd_mem hX g hn.1 hn.2 _ ih
      simp only [filt_filt] at this
      simp only [filt_congr h]
      exact this
    · have h : ∀ m, Good V.l (n + 1) m ↔ Good V.l n m := by
        intro m
        constructor
        · intro hg p hp
          exact hg p (by omega)
        · intro h2 p hp hpp hpl
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
          · exact h2 p h hpp hpl
          · exact absurd ⟨hpp, hpl⟩ hn
      simp only [filt_congr h]
      exact ih

end GlobalTheory.RowLaw.TypPart


open GlobalTheory.RowLaw.TypPart in
theorem GlobalTheory.RowLaw.typ_mem_Cv : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ a ∈ Cv X V g, ((fun i => typ V.l (a.1 i), fun q => typ V.l (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hX g a ha
  refine GlobalTheory.RowLaw.cv_closed_under_limits C V d I κ X hX g _ _ (filt_good_mem hX g a ha) fun m => ⟨m + 3, fun n hn => ⟨fun i => ?_, fun q => ?_⟩⟩
  · exact coeff_filt_good V.l_prime hX.odd _ m n hn
  · exact coeff_filt_good V.l_prime hX.odd _ m n hn
end
end

