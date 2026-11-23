module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEnd
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
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0051

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiagonalSplit
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal.MapSumDiagonal

theorem map_sum_of_pred {R Q α : Type} [AddCommMonoid R] [AddCommMonoid Q] (P : R → Prop) (f : R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (f0 : f 0 = 0)
    (fadd : ∀ a b, P a → P b → f (a + b) = f a + f b) (s : Finset α) (a : α → R) (ha : ∀ i, P (a i)) :
    P (∑ i ∈ s, a i) ∧ f (∑ i ∈ s, a i) = ∑ i ∈ s, f (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [P0, f0]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ⟨Padd _ _ (ha i) ih.1, by rw [fadd _ _ (ha i) ih.1, ih.2]⟩

theorem split_abstract {R Q Orb : Type} [Ring R] [AddCommGroup Q] [Fintype Orb] (P : R → Prop) (h : R → R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (Pmul : ∀ a b, P a → P b → P (a * b))
    (h0 : ∀ a, h a 0 = 0 ∧ h 0 a = 0)
    (hl : ∀ a a' b, P a → P a' → P b → h (a + a') b = h a b + h a' b)
    (hr : ∀ a a' b, P a → P a' → P b → h b (a + a') = h b a + h b a')
    (hs : ∀ a b, P a → P b → h b a = h a b)
    (W W' : R) (hW : P W) (hW' : P W') (hadj : ∀ a b, P a → P b → h (W * a) b = h a (W' * b))
    (hWW : W + W' = 1) (π : Orb → Fin 2 → R) (hπ : ∀ o g, P (π o g))
    (horth : ∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → h (π o g) (W * π o' g') = 0) :
    ∑ o, h (π o 0) (π o 1) = h (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) := by
  classical
  have hWπ : ∀ o g, P (W * π o g) := fun o g => Pmul _ _ hW (hπ o g)
  have e1 : (∑ o, ∑ g, π o g) = ∑ p : Orb × Fin 2, π p.1 p.2 := by rw [Fintype.sum_prod_type]
  have hB : P (∑ p : Orb × Fin 2, W * π p.1 p.2) :=
    (map_sum_of_pred P (fun _ => (0 : Q)) P0 Padd rfl (by simp) _ _ (fun p : Orb × Fin 2 => hWπ p.1 p.2)).1
  rw [e1, Finset.mul_sum]
  rw [(map_sum_of_pred P (fun a => h a (∑ p : Orb × Fin 2, W * π p.1 p.2)) P0 Padd (h0 _).2
    (fun a b ha hb => hl a b _ ha hb hB) Finset.univ (fun p : Orb × Fin 2 => π p.1 p.2)
    (fun p => hπ p.1 p.2)).2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  have e2 : ∀ g, h (π o g) (∑ p : Orb × Fin 2, W * π p.1 p.2) = h (π o g) (W * π o (1 - g)) := by
    intro g
    rw [(map_sum_of_pred P (fun a => h (π o g) a) P0 Padd (h0 _).1
      (fun a b ha hb => hr a b _ ha hb (hπ o g)) Finset.univ (fun p : Orb × Fin 2 => W * π p.1 p.2)
      (fun p => hWπ p.1 p.2)).2]
    refine Finset.sum_eq_single (o, 1 - g) ?_ (by simp)
    intro p _ hp
    apply horth
    rintro ⟨h1, h2⟩
    exact hp (Prod.ext h1.symm h2)
  rw [Fin.sum_univ_two, e2, e2, sub_zero, sub_self, ← hs _ _ (hπ o 1) (hWπ o 0),
    hadj _ _ (hπ o 0) (hπ o 1), ← hr _ _ _ (hWπ o 1) (Pmul _ _ hW' (hπ o 1)) (hπ o 0), ← add_mul, hWW, one_mul]

theorem diagonal_split : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : RawChart C d I κ), RLaw X V → ∀ (Orb : Type) [Fintype Orb] (π : Orb → Fin 2 → Matrix κ κ C) (W W' : Matrix κ κ C), (∀ o g, IntEnd X V (π o g)) → IsEnd X V W W' → W + W' = 1 → (∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → hEnd X (π o g) (W * π o' g') ∈ logInt V κ) → (∑ o, hEnd X (π o 0) (π o 1)) - hEnd X (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ := by
  intro C _ _ V d I _ κ _ _ X hR Orb _ π W W' hπ hE hWW horth
  obtain ⟨P0, Padd, Pmul, h0, hadd, hs, hadj⟩ := GlobalTheory.RowVal.EndCalc.end_calc C V d I κ X hR
  let q := QuotientAddGroup.mk' (logInt V κ)
  have hq : ∀ a, q a = 0 ↔ a ∈ logInt V κ := fun a => QuotientAddGroup.eq_zero_iff a
  have key := split_abstract (IntEnd X V) (fun a b => q (hEnd X a b)) P0 Padd Pmul
    (fun a => ⟨by simp only [(h0 a).1, map_zero], by simp only [(h0 a).2, map_zero]⟩)
    (fun a a' b ha ha' hb => by
      have := (hq _).2 (hadd a a' b ha ha' hb).1
      rw [map_sub, map_add (f := _), sub_eq_zero] at this
      exact this.symm)
    (fun a a' b ha ha' hb => by
      have := (hq _).2 (hadd a a' b ha ha' hb).2
      rw [map_sub, map_add (f := _), sub_eq_zero] at this
      exact this.symm)
    (fun a b ha hb => by
      have := (hq _).2 (hs a b ha hb)
      rwa [map_sub, sub_eq_zero] at this)
    W W' hE.1 hE.2.1
    (fun a b ha hb => by
      have := (hq _).2 (hadj W W' a b hE ha hb)
      rwa [map_sub, sub_eq_zero] at this)
    hWW π hπ (fun o g o' g' hn => (hq _).2 (horth o g o' g' hn))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hq, map_sub, map_sum, sub_eq_zero]
  exact key

end GlobalTheory.RowVal.MapSumDiagonal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiscrPowerBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerBasisDiscr

private theorem val_discr {C : Type} [Field C] (v : Valuation C NNReal) {n : ℕ} (a : Fin n → C) :
    v (discr a) = v ((Matrix.vandermonde a).det ^ 2) := by
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i j : Fin n => v (a j - a i))
  rw [Matrix.det_vandermonde, map_pow, Up.discr]
  simp only [map_prod]
  rw [sq, ← Finset.prod_mul_distrib]
  simp only [← Finset.prod_mul_distrib]
  have h2 : ∀ i : Fin n, Finset.univ.erase i = ({i}ᶜ : Finset (Fin n)) := by
    intro i; ext j; simp
  simp only [h2]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Valuation.map_sub_swap v (a i) (a j)]

private theorem inj_of_discr {C : Type} [Field C] {n : ℕ} (a : Fin n → C) (h : discr a ≠ 0) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (i := j) ?_ ?_)
  · simp [Ne.symm hne]
  · rw [hij, sub_self]

private theorem det_change {R M O : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    [Algebra R O] {n : ℕ} (b b' : Module.Basis (Fin n) R M) (f : Fin n → M →ₗ[R] O) :
    ∃ u : O, IsUnit u ∧ (Matrix.of fun i j => f j (b' i)).det = u * (Matrix.of fun i j => f j (b i)).det := by
  refine ⟨algebraMap R O (b.toMatrix b').det, ?_, ?_⟩
  · exact (b.isUnit_det b').map _
  · rw [← Matrix.det_transpose (b.toMatrix b'), RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    conv_lhs => rw [← b.sum_repr (b' i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Algebra.smul_def]

theorem discr_power_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow), (∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ)) → Function.Injective (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) ∧ 0 ≤ (w.n : ℝ) * vd ∧ (v (discr fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) : ℝ) = (v (algebraMap O C (p : O)) : ℝ) ^ ((w.n : ℝ) * vd) := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ _ w t vd hvd α b hb
  obtain ⟨b', hb'⟩ := hvd
  obtain ⟨u, hu, hdet⟩ := det_change b b'
    (fun j => (tauExt ((t j : Emb (O := O) w.e) : OE →+* O)).toLinearMap ∘ₗ w.Ow.subtype)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply] at hdet
  have hM : (Matrix.of fun i j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)) =
      (Matrix.vandermonde fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)ᵀ := by
    ext i j
    have h1 : tauExt ((t j : Emb (O := O) w.e) : OE →+* O) w.e = 1 := (t j).2
    simp [hb, h1, Matrix.vandermonde_apply]
  have hvu : v (algebraMap O C u) = 1 := hv.isUnit_iff_valuation_eq_one.1 hu
  have key : v (discr fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) =
      v (algebraMap O C (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b' i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)) := by
    rw [val_discr, hdet, hM, Matrix.det_transpose, mul_pow, map_mul, map_mul, map_pow, map_pow, map_pow,
      hvu, one_pow, _root_.one_mul, map_pow, map_pow, RingHom.map_det]
    congr 3
    ext i j
    simp [Matrix.vandermonde_apply]
  have hq0 : 0 < (v (algebraMap O C (p : O)) : ℝ) := by
    have : v (algebraMap O C (p : O)) ≠ 0 := by
      rw [map_natCast, Valuation.ne_zero_iff]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  have hq1 : (v (algebraMap O C (p : O)) : ℝ) < 1 := by
    have : v (algebraMap O C (p : O)) < 1 :=
      lt_of_le_of_ne (hv.map_le_one _) fun h => hp.out (hv.isUnit_iff_valuation_eq_one.2 h)
    exact_mod_cast this
  refine ⟨?_, ?_, by rw [key, hb']⟩
  · refine Function.Injective.of_comp (f := algebraMap O C) (inj_of_discr _ fun h0 => ?_)
    have h3 := Real.rpow_pos_of_pos hq0 ((w.n : ℝ) * vd)
    rw [← hb', ← key] at h3
    have h4 : discr (fun j => algebraMap O C (tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α)) = 0 := h0
    rw [h4] at h3
    simp at h3
  · by_contra hneg
    have h3 := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hq0 hq1 (not_le.1 hneg)
    rw [← hb'] at h3
    have h4 := hv.map_le_one (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b' i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)
    exact absurd h4 (not_le.2 (by exact_mod_cast h3))

end GlobalTheory.PowerBasisDiscr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ChF

private theorem exists_leftInv {O OE : Type} [CommRing O] [IsDomain O] [ValuationRing O] [CommRing OE] {d n : ℕ}
    (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O) (h : EigB ρ τ W) :
    ∃ G : Matrix (Fin n) (Fin d) O, ∀ i, G *ᵥ W i = Pi.single i 1 := by
  classical
  let φ : (Fin n → O) →ₗ[O] (Fin d → O) := Fintype.linearCombination O W
  have hφ : ∀ c, φ c = ∑ i, c i • W i := fun c => Fintype.linearCombination_apply O W c
  have heig : ∀ c a, (ρ a) *ᵥ φ c = τ a • φ c := by
    intro c a
    rw [hφ, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, h.1, smul_comm]
  have hinj : Function.Injective φ := by
    intro c c' hc
    obtain ⟨c₀, -, hu⟩ := h.2 (φ c) (heig c)
    rw [hu c (hφ c).symm, hu c' (by rw [hc]; exact (hφ c').symm)]
  have htf : Submodule.torsion O ((Fin d → O) ⧸ LinearMap.range φ) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨t, ht⟩, hx⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hx' : (Submodule.Quotient.mk (t • y) : (Fin d → O) ⧸ LinearMap.range φ) = 0 := by
      rw [Submodule.Quotient.mk_smul]; exact hx
    rw [Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨c, hc⟩ := hx'
    have hy : ∀ a, (ρ a) *ᵥ y = τ a • y := by
      intro a
      have := heig c a
      rw [hc, Matrix.mulVec_smul, smul_comm] at this
      exact smul_right_injective _ ht0 this
    obtain ⟨c₀, hc₀, -⟩ := h.2 y hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨c₀, (hφ c₀).trans hc₀⟩
  haveI : Module.Flat O ((Fin d → O) ⧸ LinearMap.range φ) :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htf
  haveI : Module.Free O ((Fin d → O) ⧸ LinearMap.range φ) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range φ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y, (LinearMap.id - s ∘ₗ (LinearMap.range φ).mkQ : (Fin d → O) →ₗ[O] (Fin d → O)) y ∈ LinearMap.range φ := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs ((LinearMap.range φ).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this, sub_self]
  let g : (Fin d → O) →ₗ[O] (Fin n → O) :=
    (LinearEquiv.ofInjective φ hinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hmem
  have hg : ∀ c, g (φ c) = c := by
    intro c
    have h0 : (LinearMap.range φ).mkQ (φ c) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨c, rfl⟩
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    ext1
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, h0,
      map_zero, sub_zero, LinearEquiv.ofInjective_apply]
  refine ⟨LinearMap.toMatrix' g, fun i => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, ← hg (Pi.single i 1), hφ]
  congr 1
  simp [Pi.single_apply]

theorem eigB_res_surjective : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (OE : Type) [CommRing OE] (d n : ℕ) (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O), EigB ρ τ W → Function.Surjective (Pdiv.ChartF.res W) ∧ (∀ a f, Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f) ∧ eigDim C ρ ((algebraMap O C).comp τ) = n := by
  classical
  intro C _ v O _ _ hv OE _ d n ρ τ W h
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  obtain ⟨G, hG⟩ := exists_leftInv ρ τ W h
  refine ⟨fun c => ⟨Gᵀ *ᵥ c, ?_⟩, fun a f => ?_, ?_⟩
  · have h1 : Matrix.of W * Gᵀ = 1 := by
      ext i k
      have := congrFun (hG i) k
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm (a := i), ← this, mul_comm]
    simp only [Pdiv.ChartF.res, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · ext i
    have : Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) i = W i ⬝ᵥ ((ρ a)ᵀ *ᵥ f) := rfl
    rw [this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h.1, smul_dotProduct]
    rfl
  · let W' : Fin n → Fin d → C := fun i => algebraMap O C ∘ W i
    have hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin d) O) (y : Fin d → O),
        M.map (algebraMap O C) *ᵥ (algebraMap O C ∘ y) = algebraMap O C ∘ (M *ᵥ y) := by
      intro m M y
      ext k
      exact (RingHom.map_mulVec (algebraMap O C) M y k).symm
    have hli : LinearIndependent C W' := by
      refine LinearIndependent.of_comp (Matrix.mulVecLin (G.map (algebraMap O C))) ?_
      have : (Matrix.mulVecLin (G.map (algebraMap O C))) ∘ W' = Pi.basisFun C (Fin n) := by
        funext i
        simp only [Function.comp_apply, Matrix.mulVecLin_apply, W', hmap, hG]
        ext k
        simp [Pi.single_apply, apply_ite]
      rw [this]
      exact (Pi.basisFun C (Fin n)).linearIndependent
    have hsp : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        (((algebraMap O C).comp τ) a)) = Submodule.span C (Set.range W') := by
      apply le_antisymm
      · intro x hx
        simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
        obtain ⟨⟨b, hb⟩, hbx⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
        choose y hy using hbx
        have hb0 : algebraMap O C b ≠ 0 := by
          rw [map_ne_zero_iff _ hv.hom_inj]; exact nonZeroDivisors.ne_zero hb
        have hyx : algebraMap O C ∘ y = algebraMap O C b • x := by
          ext k
          simp only [Function.comp_apply, hy k, Pi.smul_apply, Algebra.smul_def]
          rfl
        have hye : ∀ a, (ρ a) *ᵥ y = τ a • y := by
          intro a
          ext k
          apply hv.hom_inj
          have := congrFun (hmap (ρ a) y) k
          rw [hyx, Matrix.mulVec_smul, hx a, smul_comm, ← hyx] at this
          simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.comp_apply] at this
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← this]
        obtain ⟨c, hc, -⟩ := h.2 y hye
        rw [← Submodule.smul_mem_iff _ hb0, ← hyx, ← hc]
        have : algebraMap O C ∘ (∑ i, c i • W i) = ∑ i, algebraMap O C (c i) • W' i := by
          ext k
          simp [W', Finset.sum_apply, Algebra.smul_def]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        intro a
        simp only [W', hmap, h.1]
        ext k
        simp
    unfold eigDim
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsLiftIntegersIdempotentsConjugation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem existsUnique_lift_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {OE : Type} [CommRing OE] [Module.Finite ℤ OE]
    (τ : OE →+* C) : ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ := by
  have h : ∀ x : OE, ∃ y : O, algebraMap O C y = τ x := fun x => by
    have h1 : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    have h2 : IsIntegral ℤ (τ x) := h1.map τ.toIntAlgHom
    have h3 : IsIntegral O (τ x) := h2.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h3)
  choose f hf using h
  refine ⟨{ toFun := f
            map_one' := hv.hom_inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hv.hom_inj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hv.hom_inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hv.hom_inj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }, ?_, ?_⟩
  · exact RingHom.ext hf
  · intro g hg
    refine RingHom.ext fun x => hv.hom_inj ?_
    change algebraMap O C (g x) = algebraMap O C (f x)
    rw [hf, ← hg]
    rfl

theorem embeddings_idempotents_conjugation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _
  have : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  refine ⟨existsUnique_lift_integers hv, fun e τ he => ?_, ?_⟩
  · have h : IsIdempotentElem (tauExt τ e) := by
      unfold IsIdempotentElem
      rw [← map_mul, he]
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h
  · intro _ τ x
    have h2 : sig p OE x = sigE p OE x := rfl
    refine ⟨?_, h2⟩
    rw [← h2]
    clear h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [tauExt, sig]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateDatumHypothesesPeriodTower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem hodgeTateSetting_ainfTower_of_isPrimitiveRoot : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE], HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) (show O from (Ainf.ainfTowerL p O hv ε hε).c) := by
  intro p hp C _ _ _ v O _ _ hu _ hv ε hε _ OE _ _
  refine ⟨hv, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (hv.map_le_one _) (fun e => hu.out (hv.isUnit_of_one' e))
  · rw [map_natCast]
    exact fun h => Nat.cast_ne_zero.2 hp.out.ne_zero ((Valuation.zero_iff v).1 h)
  · rw [map_natCast]
    exact Ainf.c_val p O hv ε hε
  · intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have h : ∀ (x : ℤ_[p]) (y : OE), sigE p OE (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] star y := fun _ _ => rfl
      rw [h, h, star_star]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinatesStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivations_constant_in_logCoordinates : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (n : ℕ) (W : Type) [Fintype W] (Z : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (Z s) = 0) → ∀ (b : Fin n) (u : Fin dd → C) (co : W → C), (∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • MvPowerSeries.pderiv (R := C) w (Z (b', j)) = if b' = b then MvPowerSeries.C (u j) else 0) → ∀ G : PS C n dd, MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) (DofN (Y.B.FK C) b u G) = ∑ w, co w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) G) := by
  first | exact @GlobalTheory.InvDerivLog.subst_ex_DofN | exact GlobalTheory.InvDerivLog.subst_ex_DofN | (intros; apply GlobalTheory.InvDerivLog.subst_ex_DofN <;> assumption)
end

