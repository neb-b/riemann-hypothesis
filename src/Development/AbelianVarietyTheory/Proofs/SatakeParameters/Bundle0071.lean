module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCmComplexOfPow
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresRat

def conjAlg : algebraicClosure ℚ ℂ →+* algebraicClosure ℚ ℂ :=
  ((starRingEnd ℂ).comp (algebraicClosure ℚ ℂ).val.toRingHom).codRestrict (algebraicClosure ℚ ℂ) fun x => by
    have hx : IsAlgebraic ℚ (x : ℂ) := mem_algebraicClosure_iff.1 x.2
    exact mem_algebraicClosure_iff.2 (hx.algHom (starRingEnd ℂ).toRatAlgHom)

def cmComplex : Subfield ℂ :=
  (⨅ τ : algebraicClosure ℚ ℂ →+* ℂ, RingHom.eqLocusField (τ.comp conjAlg) ((starRingEnd ℂ).comp τ)).map
    (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_cmComplex {z : ℂ} : z ∈ cmComplex ↔ ∃ x : algebraicClosure ℚ ℂ, (x : ℂ) = z ∧
    ∀ τ : algebraicClosure ℚ ℂ →+* ℂ, τ (conjAlg x) = starRingEnd ℂ (τ x) := by
  unfold cmComplex
  rw [Subfield.mem_map]
  refine exists_congr fun x => ?_
  rw [Subfield.mem_iInf, and_comm]
  rfl

theorem conj_eq_inv_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : starRingEnd ℂ z = z⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz hn.ne')).symm

theorem mem_cmComplex_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ cmComplex := by
  have ha : IsAlgebraic ℚ z := IsAlgebraic.of_pow hn (by rw [hz]; exact isAlgebraic_one)
  refine mem_cmComplex.2 ⟨⟨z, mem_algebraicClosure_iff.2 ha⟩, rfl, fun τ => ?_⟩
  set x : algebraicClosure ℚ ℂ := ⟨z, mem_algebraicClosure_iff.2 ha⟩
  have hx : x ^ n = 1 := Subtype.ext hz
  have h1 : conjAlg x = x⁻¹ := Subtype.ext (conj_eq_inv_of_pow hn hz)
  rw [h1, map_inv₀, conj_eq_inv_of_pow hn (by rw [← map_pow, hx, map_one])]

theorem mem_cmComplex_iff {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (a : K) : σ a ∈ cmComplex ↔ a ∈ cmMax K := by
  let s : K →+* algebraicClosure ℚ ℂ := σ.codRestrict (algebraicClosure ℚ ℂ) fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  have hs : conjAlg (s a) = s (star a) := Subtype.ext (hσ a).symm
  rw [mem_cmComplex]
  constructor
  · rintro ⟨x, hx, h⟩ φ
    have hx' : x = s a := Subtype.ext hx
    let _ : Algebra K (algebraicClosure ℚ ℂ) := s.toAlgebra
    have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := by
      convert algebraicClosure.isAlgebraic ℚ ℂ
    have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) K
    have h1 := h (ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ)
    rw [hx', hs] at h1
    have e : ∀ b, ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ (s b) = φ b := fun b =>
      ComplexEmbedding.lift_algebraMap_apply _ φ b
    rw [e, e] at h1
    exact h1
  · intro h
    exact ⟨s a, rfl, fun τ => by rw [hs]; exact h (τ.comp s)⟩

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem act_mem (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1)
    (hρ : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i))
    (k : J) (γ : Γ) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    (PresBasic.bW P).repr ((χ k : ℂ) • ρ γ (P.coef x)) i ∈ cmComplex := by
  obtain ⟨n, hn, hk⟩ := hχ k
  have h1 : (χ k : ℂ) ∈ cmComplex :=
    mem_cmComplex_of_pow hn (by rw [← Units.val_pow_eq_pow_val, hk, Units.val_one])
  have h2 : P.coef x = ∑ j, σ (S.bV.repr x j) • P.coef (S.bV j) := by
    conv_lhs => rw [← S.bV.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h2]
  refine cmComplex.mul_mem h1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine cmComplex.sum_mem fun j _ => cmComplex.mul_mem ((mem_cmComplex_iff σ hσ _).2 (hx j)) ?_
  obtain ⟨c, hc, e⟩ := hρ γ j
  rw [e]
  simp only [← PresBasic.bW_apply]
  rw [Module.Basis.repr_sum_self]
  exact (mem_cmComplex_iff σ hσ _).2 (hc i)

end GlobalTheory.PresRat

namespace GlobalTheory

theorem classPres_dcOp_rat : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (A : Finset G) (T : Module.End K S.Forms), (∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) → (∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1) → (∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i)) → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ P A T hσ hχ hρ hT
  have hb : S.HasRatBasis := by
    refine (forms_rat S).1 fun c γ i j => ?_
    rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, P.coef_act]
    refine PresRat.act_mem P hσ hχ hρ _ _ _ (fun l => ?_) i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hb, (forms_rat S).2 T hb fun f hf c i => ?_⟩
  rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, ← PresBasic.ext_y P, hT]
  unfold dcOp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact PresRat.cmComplex.sum_mem fun a _ => PresRat.act_mem P hσ hχ hρ _ _ _ (hf _) i

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRangeSplit
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopExcess

theorem sum_range_split (f : ℕ → ℝ) (k M : ℕ) (hk : 2 ≤ k) :
    ∑ r ∈ Finset.range (k + M), f r =
      f 0 + ∑ r ∈ Finset.Ico 1 (k - 1), f r + f (k - 1) + ∑ r ∈ Finset.Ico k (k + M), f r := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← Finset.sum_range_add_sum_Ico f (Nat.le_add_right (n + 1) M), Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico f (by omega : 1 ≤ n), Finset.sum_range_one]

theorem sum_Ico_bounds (f : ℕ → ℝ) (a b : ℕ) (lo hi : ℝ) (h : ∀ r, a ≤ r → r < b → lo ≤ f r ∧ f r ≤ hi) :
    ((b - a : ℕ) : ℝ) * lo ≤ ∑ r ∈ Finset.Ico a b, f r ∧ ∑ r ∈ Finset.Ico a b, f r ≤ ((b - a : ℕ) : ℝ) * hi := by
  constructor
  · have := Finset.card_nsmul_le_sum (Finset.Ico a b) f lo
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).1)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this
  · have := Finset.sum_le_card_nsmul (Finset.Ico a b) f hi
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).2)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this

theorem top_excess : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x5, h5⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨⟨g1, g2⟩, g3, g4⟩, g5⟩ := hx
  obtain ⟨a1, a2, a3, -, a5, a6, -, -, a9, -⟩ := h1 x g1 hx1 i
  obtain ⟨b1, -, b3⟩ := h2 x g2 hx1 i j hj z
  obtain ⟨b3, -⟩ := b3 hz
  have c := h3 x g3 hx1 i u j hj z
  obtain ⟨-, -, d3, d4⟩ := h4 x g4 hx1 i u j hj z hz
  have e := h5 x g5 hx1 i u j hj z
  clear h1 h2 h3 h4 h5
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.N j = D.R.k + j * (D.R.t + 1) := by unfold Ranks.N; omega
  have hok := nuRowOK D
  rw [GlobalTheory.nuD_card_eq_sum_nuRow D hok u j hj z, hok u j hj z 0, if_pos (by omega), hN,
    sum_range_split _ _ _ (by omega)]
  obtain ⟨m1, m2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) 1 (D.R.k - 1) _ _
    (fun r hr1 hr2 => let h := (c r (by omega)).2 hz hr1 (by omega); ⟨h.1.le, h.2.le⟩)
  obtain ⟨n1, n2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) D.R.k (D.R.k + j * (D.R.t + 1)) _ _
    (fun r hr1 hr2 => e r hr1 (by omega))
  have hkc : ((D.R.k - 1 - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num
  rw [hkc] at m1 m2
  rw [Nat.add_sub_cancel_left] at n1 n2
  push_cast at n1 n2
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj.le
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) a6
  have hbl : (j : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by gcongr
  have hS1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hS.le (by linarith)
  rw [mul_div_assoc] at d4
  constructor <;> nlinarith

end GlobalTheory.TopExcess
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.InertCompare

section Emb

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom

def rhoH (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem rhoH_apply (τ : D.what₂.Tau) (x : D.host.E) : rhoH D lam τ x = lamC lam (embT D τ x) := by
  unfold lamC
  rw [dite_eq_left (embT_mem D τ x)]
  rfl

theorem coe_rhoH (τ : D.what₂.Tau) : (rhoH D lam τ : D.host.E → ℂ_[l]) = tauEmb D lam τ :=
  funext fun x => rhoH_apply D lam τ x

def rhoC (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] := (rhoH D lam τ).comp (D.host.conj : D.host.E →+* D.host.E)

end Emb

def SamePrime {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ ρ' : E →+* ℂ_[l]) : Prop :=
  ∀ a : 𝓞 E, ‖ρ (a : E)‖ < 1 ↔ ‖ρ' (a : E)‖ < 1

theorem tauPl_bijective (D : D7) : Function.Bijective (tauPl D) := by
  have hinj := D.R.toFrame.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h1 : plGG D (b, t) = plGG D (b', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases b <;> cases b' <;> simp only [plGG, if_true, if_false, Bool.false_eq_true] at h1
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
    · exact absurd h1 (hP.2 _ _)
    · exact absurd h1.symm (hP.2 _ _)
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨(false, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])
    · refine ⟨(true, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])

def plEquiv (D : D7) : (Bool × HH D) ≃ D.what₂.Tau := Equiv.ofBijective _ (tauPl_bijective D)

end GlobalTheory.InertCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorLatSpan
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.StdBaseChange

def pureSet (K : Type) [CommRing K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) : Set (MvPolynomial (S × (Fin k × Fin n)) K) :=
  {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ A s) ∧ P = ∏ s, blockEmb K s (F s)}

theorem tensorLat_span (R K : Type) [CommRing R] [CommRing K] [Algebra R K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    tensorLat R K (fun s => Submodule.span R (A s)) = Submodule.span R (pureSet K A) := by
  classical
  apply le_antisymm
  · unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (blockEmb K s '' A s) := fun s =>
      Submodule.apply_mem_span_image_of_mem_span ((blockEmb K s).toLinearMap.restrictScalars R) (hF s)
    have h2 : ∀ t : Finset S, ∏ s ∈ t, blockEmb K s (F s) ∈ ∏ s ∈ t, Submodule.span R (blockEmb K s '' A s) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.prod_empty]
        exact Submodule.one_le.mp le_rfl
      | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact Submodule.mul_mem_mul (h1 a) ih
    have h3 := h2 Finset.univ
    rw [Submodule.prod_span] at h3
    refine Submodule.span_mono ?_ h3
    intro P hP
    obtain ⟨G, hG, rfl⟩ := (Set.mem_fintype_prod _ _).mp hP
    choose F' hF' hFG using hG
    exact ⟨F', hF', by simp only [hFG]⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => Submodule.subset_span (hF s), rfl⟩

theorem image_pureSet {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    MvPolynomial.map φ '' pureSet K A = pureSet L fun s => MvPolynomial.map φ '' A s := by
  have h : ∀ F : S → MvPolynomial (Fin k × Fin n) K,
      MvPolynomial.map φ (∏ s, blockEmb K s (F s)) = ∏ s, blockEmb L s (MvPolynomial.map φ (F s)) := by
    intro F
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [blockEmb, map_rename]
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨_, fun s => ⟨F s, hF s, rfl⟩, h F⟩
  · rintro ⟨G, hG, rfl⟩
    choose F hF hFG using hG
    exact ⟨_, ⟨F, hF, rfl⟩, by rw [h]; simp only [hFG]⟩

theorem span_map_span {R K O L σ : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing O] [CommRing L] [Algebra O L]
    (φ : K →+* L) (ψ : R →+* O) (h : ∀ r, algebraMap O L (ψ r) = φ (algebraMap R K r)) (T : Set (MvPolynomial σ K)) :
    Submodule.span O (MvPolynomial.map φ '' (Submodule.span R T : Set (MvPolynomial σ K))) =
      Submodule.span O (MvPolynomial.map φ '' T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      have e : MvPolynomial.map φ (a • y) = ψ a • MvPolynomial.map φ y := by
        rw [← algebraMap_smul K a y, ← algebraMap_smul L (ψ a), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, h]
      rw [e]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem dualWeyl_map (R K : Type) [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (dualWeyl R n n ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.bidSet K n ν) := by
  rw [StdDual.dualWeyl_eq, Submodule.map_span, ← StdDual.image_bidSet (algebraMap R K)]
  rfl

theorem weyl_map (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (weyl R n n le_rfl ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.wordSet K n ν) := by
  rw [StdDual.weyl_eq, Submodule.map_span, ← StdDual.image_wordSet (algebraMap R K)]
  rfl

theorem std_baseChange : ∀ (O Kf K ι : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Field K] [NumberField K] [Fintype ι] (eK : K →+* Kf) (ψ : 𝓞 K →+* O), (∀ r, algebraMap O Kf (ψ r) = eK r) → ∀ (n : ℕ) (lam : ι → DomWeight n), Submodule.span O (MvPolynomial.map eK '' (nabStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdN O Kf n (lam τ).natW) ∧ Submodule.span O (MvPolynomial.map eK '' (delStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdD O Kf n (lam τ).natW) := by
  intro O Kf K ι _ _ _ _ _ _ _ eK ψ h n lam
  constructor
  · have e : nabStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.bidSet K n (lam τ).natW) := by
      unfold nabStd
      congr 1
      funext τ
      exact dualWeyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdN, dualWeyl_map, StdDual.image_bidSet]
    rw [tensorLat_span]
  · have e : delStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.wordSet K n (lam τ).natW) := by
      unfold delStd
      congr 1
      funext τ
      exact weyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdD, weyl_map, StdDual.image_wordSet]
    rw [tensorLat_span]

end GlobalTheory.StdBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoWLeFirstRow
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopFirstRow

theorem two_w_le_first_row : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 2 * wPl (Fm.D x i) (j + 1) z ≤ (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  refine ⟨max x1 (max x2 x3), fun x hx hx1 i u j hj z hz => ?_⟩
  have hxa : x ≥ x1 := le_trans (le_max_left _ _) hx
  have hxb : x ≥ x2 := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hxc : x ≥ x3 := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx
  obtain ⟨-, -, -, -, -, h4, h2b, -, -, -⟩ := h1 x hxa hx1 i
  obtain ⟨e1, e2, e3, -⟩ := h2 x hxb hx1 i u j hj z hz
  obtain ⟨-, -, hw⟩ := h3 x hxc hx1 i j hj z
  obtain ⟨-, hw2⟩ := hw hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have ha : aL L z.2 = L.aT ⟨z.2, hz.2⟩ := by unfold aL; rw [dite_eq_left hz.2]
  have hbb : bL L z.2 = L.bT ⟨z.2, hz.2⟩ := by unfold bL; rw [dite_eq_left hz.2]
  have a1 := (L.aT_win ⟨z.2, hz.2⟩).1
  have a2 := L.bT_ge ⟨z.2, hz.2⟩
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hN : 0 < D.R.N j := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  rw [nuRowOK D u j hj z 0, if_pos hN, e1]
  rw [e2, hbb] at e3
  rw [ha]
  linarith

end GlobalTheory.TopFirstRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WPlPos
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.Ggeo

theorem wPl_pos : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), 0 < wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨y0, h1⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  refine ⟨max x0 y0, fun x hx hx1 i j hj z => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hw, -⟩ := h0 x (le_trans (le_max_left _ _) hx) hx1 i
  have h2 := (h1 x (le_trans (le_max_right _ _) hx) hx1 i j hj z).1
  linarith

end GlobalTheory.Ggeo
end

