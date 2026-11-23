module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerOfRelativeTraceNormIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

theorem integral_of_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t →
    w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  intro D w t n ht hn
  have hint : ∀ s : 𝓞 D.host.F, IsIntegral ℤ (algebraMap D.host.F D.host.E s) := fun s =>
    (NumberField.RingOfIntegers.isIntegral_coe s).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  let t' : 𝓞 D.host.E := ⟨algebraMap D.host.F D.host.E t, hint t⟩
  let n' : 𝓞 D.host.E := ⟨algebraMap D.host.F D.host.E n, hint n⟩
  have hw : IsIntegral (𝓞 D.host.E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C n', ?_, ?_⟩
    · monicity!
    · have h1 : algebraMap (𝓞 D.host.E) D.host.E t' = w + D.sp.cm.sig w := ht.symm
      have h2 : algebraMap (𝓞 D.host.E) D.host.E n' = w * D.sp.cm.sig w := hn.symm
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2]
      ring
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E) (K := D.host.E)).mp hw
  exact ⟨y, hy⟩

end GlobalTheory.FixedUnitNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IwaPlace

variable {D : D7}


open GlobalTheory.SelfDualAt in
theorem idAt₂ (v : Pl D) : algebraMap (AF D.host.F) (AE D) (cP (· = v)) ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · rw [RingHom.mem_ker]
    show infPart D (cP (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    exact TensorProduct.zero_tmul _ _
  · rw [RingHom.mem_ker]
    show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (finPart D (algebraMap (AF D.host.F) (AE D) (cP (· = v)))) = 0
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (sndA D.host.F (cP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w.1 (indP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      rfl
    rw [h, evalV_indP, if_neg w.2]
    exact TensorProduct.zero_tmul _ _


open GlobalTheory.SelfDualAt in
theorem eq_alg_cP {v : Pl D} {ε : AE D} (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) :
    ε = algebraMap (AF D.host.F) (AE D) (cP (· = v)) := by
  have h1 := algebraMap_placeIdempotent_mul (· = v) ε hεI.1
  have h2 := (hε _).1 (idAt₂ v)
  rw [← h2, mul_comm]
  exact h1.symm


open GlobalTheory.SelfDualAt in
theorem placeIdem_eq_cP {v : Pl D} {εF : AF D.host.F} (h : IsPlaceIdem D v εF) : εF = cP (· = v) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  unfold cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  show evalV D.host.F w α = evalV D.host.F w (indP (· = v))
  rw [evalV_indP]
  by_cases hw : w = v
  · subst hw; rw [if_pos rfl, h1]
  · rw [if_neg hw, h0 w hw]

theorem half_mem_int (v : Pl D) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) :
    algebraMap D.host.F (Fv D.host.F v) (2⁻¹) ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e1 : Valued.v (algebraMap D.host.F (Fv D.host.F v) 2⁻¹) = v.valuation D.host.F 2⁻¹ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have e2 : v.valuation D.host.F (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) v (2 : 𝓞 D.host.F)
    simp only [map_ofNat] at this
    rw [this]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
  rw [e1, map_inv₀, e2, inv_one]


open GlobalTheory.SelfDualAt in
theorem exists_trace_one_at_tame : ∀ (D : D7) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v →
    ∃ w ∈ intAt D (· = v), w + cA D w = ε := by
  intro D v ε _ _ hεI hε ht
  have hεη := eq_alg_cP hεI hε
  rcases ht.2 with h2 | ⟨e, εF, hsp, hpl, hsum⟩
  · refine ⟨algebraMap (AF D.host.F) (AE D) (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul]
      exact Ideal.mul_mem_right _ _ (idAt₂ v)
    · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
      refine AddSubgroup.subset_closure ⟨sndA D.host.F (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), fun w => ?_, 1, by simp⟩
      rw [map_mul, AlgHom.commutes, map_mul]
      show evalV D.host.F w (indP (· = v)) * _ ∈ _
      rw [evalV_indP]
      by_cases hw : w = v
      · subst hw
        rw [if_pos rfl, one_mul, AlgHom.commutes]
        exact half_mem_int w h2
      · rw [if_neg hw, zero_mul]
        exact zero_mem _
    · rw [cA_alg, ← map_add (f := _), hεη]
      congr 1
      rw [← two_mul, mul_left_comm, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul,
        mul_inv_cancel₀ two_ne_zero, map_one, mul_one]
  · have hs : e + cA D e = ε := by rw [hsum, placeIdem_eq_cP hpl, hεη]
    refine ⟨e, ⟨?_, ?_⟩, hs⟩
    · have : e * ε = e := by rw [← hs, mul_add, hsp.1, hsp.2.1, add_zero]
      rw [← this]
      exact Ideal.mul_mem_left _ _ hεI.1
    · exact GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hsp.1])

end GlobalTheory.IwaPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.DualIso

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_mul_mem {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem hermAt_smul_left (S : HSp D) (o : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (o • y) x = o * hermAt S y x := by
  simp only [hermAt, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem smul_mem_of_isSDAt {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {o : AE D} (ho : o ∈ intAt D (· = v)) {y : Fin S.rank → AE D} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM.2.2 _ fun i => ?_).2 fun x hx => ?_
  · simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hM.1 y hy i)
  · rw [hermAt_smul_left]; exact intAt_mul_mem ho ((hM.2.2 y (hM.1 y hy)).1 hy x hx)

theorem col_mul_mem {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M) {ρ : ℕ}
    (A : Mx D S.rank ρ) (B : Mx D ρ ρ) (hA : ∀ i, (fun k => A k i) ∈ M) (hB : ∀ m i, B m i ∈ intAt D (· = v))
    (i : Fin ρ) : (fun k => (A ⬝ B) k i) ∈ M := by
  have e : (fun k => (A ⬝ B) k i) = ∑ m, B m i • (fun k => A k m) := by
    funext k; simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [e]; exact AddSubgroup.sum_mem _ fun m _ => smul_mem_of_isSDAt hM (hB m i) (hA m)

theorem gram_entry (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) (i j : Fin ρ) :
    (adj c' ⬝ (gA S ⬝ c')) i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
  simp only [hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem smul_mul_smul_one {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (ε • (1 : Mx D ρ ρ)) ⬝ (w • H) = (ε * w) • H := by
  rw [smul_mul_assoc, one_mul, smul_smul]

theorem smul_mul_smul_one' {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (w • H) ⬝ (ε • (1 : Mx D ρ ρ)) = (ε * w) • H := by
  rw [mul_smul_comm, mul_one, smul_smul]

theorem adj_gram_self (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) : adj (adj c' ⬝ (gA S ⬝ c')) = adj c' ⬝ (gA S ⬝ c') := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem gram_swap_smul (S : HSp D) {ρ : ℕ} {ε : AE D} (hεc : cA D ε = ε) (c c' : Mx D S.rank ρ)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ) := by
  have := congrArg adj hcc
  rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at this

theorem pair_sub (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc0 : adj c ⬝ (gA S ⬝ c) = 0) (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero, sub_zero, hcc]

theorem pair_sub' (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc' : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c') = adj c' ⬝ (gA S ⬝ c') - adj K ⬝ (ε • (1 : Mx D ρ ρ)) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']

theorem self_sub (S : HSp D) {ρ : ℕ} (c'' c c' : Mx D S.rank ρ) (K : Mx D ρ ρ) (h : c'' = c' - c ⬝ K) :
    adj c'' ⬝ (gA S ⬝ c'') = adj c'' ⬝ (gA S ⬝ c') - adj c'' ⬝ (gA S ⬝ c) ⬝ K := by
  rw [h, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
    ← Matrix.mul_assoc (adj (c' - c ⬝ K)) (gA S ⬝ c) K]

theorem isotropic_core {S : HSp D} {v : Pl D} {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {w : AE D} (hw : w ∈ intAt D (· = v)) (hwc : w + cA D w = ε) {ρ : ℕ} (c c' : Mx D S.rank ρ)
    (hc : ∀ i, (fun k => c k i) ∈ M) (hc' : ∀ i, (fun k => c' k i) ∈ M) (hcc0 : adj c ⬝ (gA S ⬝ c) = 0)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) ∧
      adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  obtain ⟨H, hH⟩ : ∃ H : Mx D ρ ρ, H = adj c' ⬝ (gA S ⬝ c') := ⟨_, rfl⟩
  have hHint : ∀ i j, H i j ∈ intAt D (· = v) := fun i j => by
    rw [hH, gram_entry]; exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by rw [hH]; exact adj_gram_self S c'
  have hcc' := gram_swap_smul S hεc c c' hcc
  have hKint : ∀ m i, (w • H) m i ∈ intAt D (· = v) := fun m i => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact intAt_mul_mem hw (hHint m i)
  have e3 : ε * cA D w + ε * w = ε := by rw [← mul_add, add_comm, hwc, hεε]
  have f3 : H - (ε * cA D w) • H - (ε * w) • H = 0 := by
    rw [sub_sub, ← add_smul, e3, hεH, sub_self]
  have e1 := pair_sub S (ε := ε) c c' (w • H) hcc0 hcc
  have e2 := pair_sub' S c c' (w • H) hcc'
  rw [← hH, adj_smul, hadjH, smul_mul_smul_one'] at e2
  refine ⟨c' - c ⬝ (w • H), fun i => ?_, e1, ?_⟩
  · have e : (fun k => (c' - c ⬝ (w • H)) k i) = (fun k => c' k i) - fun k => (c ⬝ (w • H)) k i := rfl
    rw [e]; exact sub_mem (hc' i) (col_mul_mem hM c _ hc hKint i)
  · rw [self_sub S _ c c' (w • H) rfl, e1, e2, smul_mul_smul_one, f3]
theorem dual_isotropic : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  have hcc0 : adj (d.jX ⬝ b) ⬝ (gA S ⬝ (d.jX ⬝ b)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b, ← Matrix.mul_assoc (adj d.jX),
      d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  exact isotropic_core hεε hεc hε hM hw hwc (d.jX ⬝ b) c' hc hc' hcc0 hcc

end GlobalTheory.IwaPlace.DualIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaxCompactRealPointsOfOrthonormalFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

noncomputable section

namespace GlobalTheory.FrameCompact

open GlobalTheory.SmoothForms Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

def comps (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : ∀ τ, Formalism.REAL.KG (ε τ)) : AlgInf V :=
  fun τ => (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ

theorem comps_unit (R : RealPoints θ V) (h : IsFrameFam V ε fr) (k : ∀ τ, Formalism.REAL.KG (ε τ)) :
    sigInf V (comps fr k) * comps fr k = 1 :=
  (unit_iff R _).2 fun τ => conj_mem_UH (h τ).1 (h τ).2 (k τ)

theorem continuous_comps : Continuous (comps (ε := ε) fr) := by
  have key : Continuous fun (k : ∀ τ, Formalism.REAL.KG (ε τ)) (τ : D.what₂.Tau) =>
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ := by
    refine continuous_pi fun τ => ?_
    have h1 : Continuous fun k : Formalism.REAL.KG (ε τ) => Formalism.REAL.toMK k :=
      (Formalism.REAL.isClosedEmbeddingMatrix _ (ε τ)).1.continuous.comp continuous_subtype_val
    exact (continuous_const.matrix_mul (h1.comp (continuous_apply τ))).matrix_mul continuous_const
  exact key

def frameHom (R : RealPoints θ V) (h : IsFrameFam V ε fr) : (∀ τ, Formalism.REAL.KG (ε τ)) →* GA D V :=
  MonoidHom.mk' (fun k => secInf θ V (comps fr k)) fun k l => by
    have a := secInf_spec R (comps_unit R h k)
    have b := secInf_spec R (comps_unit R h l)
    have c := secInf_spec R (comps_unit R h (k * l))
    refine R.2.2.1 _ c.1 _ (mul_mem a.1 b.1) fun τ => ?_
    have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
    rw [R.2.2.2.1, c.2, a.2, b.2]
    change (fr τ)⁻¹ * (Formalism.REAL.toMK (k τ) * Formalism.REAL.toMK (l τ)) * fr τ =
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ * ((fr τ)⁻¹ * Formalism.REAL.toMK (l τ) * fr τ)
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]

theorem frameHom_spec (R : RealPoints θ V) (h : IsFrameFam V ε fr) (k : ∀ τ, Formalism.REAL.KG (ε τ)) :
    frameHom R h k ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (frameHom R h k) =
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ :=
  secInf_spec R (comps_unit R h k)

theorem frameHom_single (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) (τ : D.what₂.Tau)
    (k : Formalism.REAL.KG (ε τ)) : frameHom R h (Pi.mulSingle τ k) = kAt θ V τ (ε τ) (fr τ) k := by
  have a := frameHom_spec R h (Pi.mulSingle τ k)
  have b := isAtTau_kAt θ V hθ τ (h τ).1 (h τ).2 k
  refine R.2.2.1 _ a.1 _ b.1 fun τ' => ?_
  rw [a.2]
  by_cases c : τ' = τ
  · subst c
    rw [b.2.1, Pi.mulSingle_eq_same]
  · rw [b.2.2 _ c, Pi.mulSingle_eq_of_ne c]
    change (fr τ')⁻¹ * 1 * fr τ' = 1
    rw [Matrix.mul_one, nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (h τ').1)]

theorem isCompact_frameRange (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) :
    IsCompact ((frameHom R h).range : Set (GA D V)) := by
  have hc : Continuous (frameHom R h) :=
    (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous continuous_comps (comps_unit R h)
  rw [MonoidHom.coe_range]
  exact _root_.isCompact_range hc

theorem conj_mem_Kset (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) (K' : Subgroup (GA D V))
    (hc : IsCompact (K' : Set (GA D V))) (hle : (frameHom R h).range ≤ K') (τ : D.what₂.Tau) {g : GA D V}
    (hg : g ∈ K') : fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹ ∈ Formalism.REAL.Kset (ε τ) := by
  have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
  let f : GA D V → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun g => fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹
  have fc : Continuous f :=
    (continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ))).matrix_mul continuous_const
  have fm : ∀ a b, f (a * b) = f a * f b := fun a b => by
    simp only [f, R.2.2.2.1, Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd]
  have fk : ∀ k, f (frameHom R h k) = Formalism.REAL.toMK (k τ) := fun k => by
    simp only [f, (frameHom_spec R h k).2, Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd, mul_nonsing_inv _ hd, Matrix.mul_one]
  have f1 : f 1 = 1 := by
    rw [← map_one (frameHom R h), fk]
    rfl
  have key := _root_.GlobalTheory.BoundedUnitary.eq_Kset_of_bounded V.rank (ε τ) (f '' K') ?_ ?_ ?_ ?_ ?_
  · rw [← key]
    exact ⟨g, hg, rfl⟩
  · rintro _ ⟨a, -, rfl⟩
    have hu : (infMat D.sp.cm.sig V.gram (θ τ) a)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) a = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
    have h1 : ((fr τ)⁻¹)ᴴ * (fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
    change (f a)ᴴ * Formalism.REAL.Jm (ε τ) * f a = Formalism.REAL.Jm (ε τ)
    calc (f a)ᴴ * Formalism.REAL.Jm (ε τ) * f a
        = ((fr τ)⁻¹)ᴴ * ((infMat D.sp.cm.sig V.gram (θ τ) a)ᴴ * ((fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ) *
            infMat D.sp.cm.sig V.gram (θ τ) a) * (fr τ)⁻¹ := by
          simp only [f, conjTranspose_mul, Matrix.mul_assoc]
      _ = (((fr τ)⁻¹)ᴴ * (fr τ)ᴴ) * Formalism.REAL.Jm (ε τ) * (fr τ * (fr τ)⁻¹) := by
          rw [(h τ).2, hu, ← (h τ).2]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · rw [← Formalism.REAL.range_toMK]
    rintro _ ⟨k, rfl⟩
    refine ⟨frameHom R h (Pi.mulSingle τ k), hle ⟨_, rfl⟩, ?_⟩
    rw [fk, Pi.mulSingle_eq_same]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, fm a b⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, (inv_eq_left_inv ?_).symm⟩
    rw [← fm, inv_mul_cancel, f1]
  · have : ∀ i j, ∃ C : ℝ, ∀ a ∈ K', ‖f a i j‖ ≤ C := fun i j =>
      hc.exists_bound_of_continuousOn (fc.matrix_elem i j).continuousOn
    choose C hC using this
    obtain ⟨B, hB⟩ := (Set.finite_range fun p : Fin V.rank × Fin V.rank => C p.1 p.2).bddAbove
    refine ⟨B, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ i j
    exact (hC i j a ha).trans (hB ⟨(i, j), rfl⟩)

theorem isMaxCompactInf_range (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) :
    IsMaxCompactInf V (frameHom R h).range := by
  refine ⟨?_, isCompact_frameRange hθ R h, fun K' hi hc hle => le_antisymm (fun g hg => ?_) hle⟩
  · rintro _ ⟨k, rfl⟩
    exact (frameHom_spec R h k).1
  · have : ∀ τ, ∃ k : Formalism.REAL.KG (ε τ),
        Formalism.REAL.toMK k = fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹ := fun τ => by
      have := conj_mem_Kset hθ R h K' hc hle τ hg
      rw [← Formalism.REAL.range_toMK] at this
      exact this
    choose k hk using this
    refine ⟨k, R.2.2.1 _ (frameHom_spec R h k).1 _ (hi g hg) fun τ => ?_⟩
    have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
    rw [(frameHom_spec R h k).2, hk]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, Matrix.mul_one]

theorem exists_maxCompact_of_frames : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∃ K : Subgroup (GA D V), IsMaxCompactInf V K ∧ (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) := by
  intro D θ hθ V ε fr h
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  exact ⟨(frameHom R h).range, isMaxCompactInf_range hθ R h, (frameHom R h).rangeRestrict,
    (frameHom R h).rangeRestrict_surjective, fun τ k => frameHom_single hθ R h τ k⟩

end GlobalTheory.FrameCompact

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenAddSubgroupFinitePoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

namespace GlobalTheory.FinSubgroup

theorem exists_openAddSubgroup_finite_points :
    ∀ (D : D7) (V : Set (AE D)), V ∈ nhds (0 : AE D) →
      ∃ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) ∧ ∀ a ∈ U, infPart D a = 0 → a ∈ V := by
  intro D V hV
  obtain ⟨e, he, hc, hcs⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)
  letI : TopologicalSpace (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (InfiniteAdeleRing D.host.F) (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E)
  have h0 : e.symm 0 = 0 := map_zero _
  have hV' : (e.symm : _ → AE D) ⁻¹' V ∈ 𝓝 ((0 : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E),
      (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) := by
    apply hcs.continuousAt.preimage_mem_nhds
    have : (e.symm : _ → AE D) (0, 0) = 0 := h0
    rw [this]
    exact hV
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hV'
  obtain ⟨N, hN, hNB⟩ := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (Subsingleton.elim _ _)).2 B hB
  let W : AddSubgroup (GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    (GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E))).map (nsmulAddMonoidHom N)
  have hW : IsOpen (W : Set (GlobalTheory.AdLat.RA D.host.F D.host.E)) := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    convert this using 1
    ext z
    simp only [W, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, nsmulAddMonoidHom_apply, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  let f : AE D →+ GlobalTheory.AdLat.RA D.host.F D.host.E := (AddMonoidHom.snd _ _).comp e.toAddMonoidHom
  have hf : Continuous f := continuous_snd.comp hc
  refine ⟨W.comap f, hW.preimage hf, fun a ha hinf => ?_⟩
  have h1 : (e a).1 = 0 := by rw [(he a).1]; exact hinf
  have h2 : (e a).2 ∈ B := by
    obtain ⟨y, hy, hya⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_comap.1 ha)
    have : f a = (e a).2 := rfl
    rw [← this, ← hya]
    exact hNB y hy
  have h3 : e a ∈ A ×ˢ B := ⟨by rw [h1]; exact mem_of_mem_nhds hA, h2⟩
  have := hAB h3
  simpa using this

end GlobalTheory.FinSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinsetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset : ∀ (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S), (∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) → Filter.Tendsto x Filter.atTop (nhds κ) := by
  first | exact @GlobalTheory.AdelicLimit.tendsto_of_agree | exact GlobalTheory.AdelicLimit.tendsto_of_agree | (intros; apply GlobalTheory.AdelicLimit.tendsto_of_agree <;> assumption)
end

