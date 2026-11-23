module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

open scoped UpperHalfPlane nonZeroDivisors Real

theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 : eisG Λ k = ∑' z : ℂ, ({w : ℂ | w ∈ Λ ∧ w ≠ 0}).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, eisG]
    exact tsum_congr fun w => one_div _
  have h2 : L.G (2 * k) = ∑' z : ℂ, (L.lattice : Set ℂ).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, PeriodPair.G]
    rfl
  rw [h1, h2]
  refine tsum_congr fun z => ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hz, h]

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha

theorem indep_of_tau : LinearIndependent ℝ ![a * (τ : ℂ), a] := by
  rw [LinearIndependent.pair_iff]
  intro s t e
  have e2 : (s * τ + t : ℂ) = 0 := mul_left_cancel₀ ha (by
    simp only [Complex.real_smul] at e
    linear_combination e)
  have e3 : s = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
  exact ⟨e3, by simpa [e3] using e2⟩

include h

omit ha in
theorem eq_closure_of_tau : Λ = AddSubgroup.closure {a * (τ : ℂ), a} := by
  ext x
  rw [h, AddSubgroup.mem_closure_pair]
  refine exists_congr fun m => exists_congr fun n => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, show (m : ℂ) * (a * τ) + n * a = a * (m * τ + n) by ring]

theorem discr_of_tau : TaylorLogMetric.discr Λ = (2 * π / a) ^ 12 * ModularForm.discriminant τ := by
  let L : PeriodPair := ⟨a * τ, a, indep_of_tau ha⟩
  have hL : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := fun x => by
    rw [PeriodPair.mem_lattice]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [show (m : ℂ) * L.ω₁ + n * L.ω₂ = a * (m * τ + n) by simp only [L]; ring]
  have hh : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by rw [h, hL]
  rw [← latticeCurve_Δ_eq_discriminant ha hL, latticeCurve_Δ, TaylorLogMetric.discr, g2, g3,
    eisG_eq_G L Λ hh (by norm_num), eisG_eq_G L Λ hh (by norm_num)]
  rfl

theorem area_of_tau : area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hp : 0 < ‖a‖ ^ 2 * τ.im := by have := norm_pos_iff.2 ha; positivity
  have key : ∀ m n m' n' : ℤ, |((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im| =
      ‖a‖ ^ 2 * τ.im * |((n * m' - m * n' : ℤ) : ℝ)| := fun m n m' n' => by
    rw [← abs_of_pos hp, ← abs_mul]
    congr 1
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨hp, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩
    rw [key]
    simp
  · rintro r ⟨hr, w₁, h1, w₂, h2, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h1
    obtain ⟨m', n', rfl⟩ := (h _).1 h2
    rw [key] at hr ⊢
    have h0 : (n * m' - m * n' : ℤ) ≠ 0 := fun e => by simp [e] at hr
    have : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_right hp.le this

end

theorem mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ w : ℂ) :
    w ∈ lamOf D cc δ ↔ ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem finrank_hostK (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K D.host.hyp.2.1.pos (D.host.sqd_sq)

theorem discr_hostK (D : D7) : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_hostK D) D.host.hyp.2.1.squarefree
    (by have := D.host.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq))

theorem exists_tau (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ (Ideal.absNorm cc : ℝ) = 2 * ‖a‖ ^ 2 * τ.im / √(D.host.d) ∧
      ∀ δ x : ℂ, x ∈ lamOf D cc δ ↔ ∃ m n : ℤ, δ * a * (m * (τ : ℂ) + n) = x := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let I : (Ideal (𝓞 D.host.K))⁰ := ⟨cc, mem_nonZeroDivisors_of_ne_zero hcc⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_hostK D) (discr_hostK D) σ
    (FractionalIdeal.mk0 D.host.K I)
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have h' : ∀ z, z ∈ σ '' (cc : FractionalIdeal (𝓞 D.host.K)⁰ D.host.K) ↔
      ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = z := fun z => by
    rw [← h, ← SetLike.mem_coe, hL]
    rfl
  have hN := QuadraticZeta.absNorm_eq_of_image (finrank_hostK D) (discr_hostK D) σ ha h'
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at hN
  refine ⟨a, τ, ha, hN, fun δ x => ?_⟩
  rw [mem_lamOf]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := (h' _).1 ⟨(c : D.host.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
    exact ⟨m, n, by rw [mul_assoc, e]; rfl⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨y, hy, e⟩ := (h' _).2 ⟨m, n, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, by rw [mul_assoc, ← e]; rfl⟩

theorem lattice_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧ δ ≠ 0 ∧ TaylorLogMetric.discr (lamOf D cc δ) = 1 ∧ area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ (∀ a : 𝓞 D.host.K, ∀ w ∈ (lamOf D cc δ), D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ (lamOf D cc δ)) := by
  intro D _ cc δ ⟨⟨hcc, _⟩, hδ⟩
  obtain ⟨a, τ, ha, hN, h⟩ := exists_tau D cc hcc
  have h1 := discr_of_tau (by simpa using ha) (h 1)
  rw [one_mul] at h1
  have hδ' : δ ^ 12 = (2 * π / a) ^ 12 * ModularForm.discriminant τ := hδ.trans h1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have := ModularForm.discriminant_ne_zero τ
    have := Real.pi_ne_zero
    simp [*] at hδ'
  have hda : δ * a ≠ 0 := mul_ne_zero hδ0 ha
  refine ⟨⟨_, _, indep_of_tau (τ := τ) hda, eq_closure_of_tau (h δ)⟩, hδ0, ?_, ?_, ?_⟩
  · rw [discr_of_tau hda (h δ), show (2 * π / (δ * a) : ℂ) ^ 12 * ModularForm.discriminant τ =
      ((2 * π / a) ^ 12 * ModularForm.discriminant τ) / δ ^ 12 by field_simp, ← hδ',
      div_self (pow_ne_zero _ hδ0)]
  · have hd : 0 < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    rw [area_of_tau hda (h δ), hN, norm_mul]
    field_simp
  · intro b w hw
    obtain ⟨c, hc, rfl⟩ := (mem_lamOf D cc δ w).1 hw
    exact (mem_lamOf D cc δ _).2 ⟨b * c, cc.mul_mem_left b hc, by simp; ring⟩

end GlobalTheory.CurveLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.InducedType

open Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK

theorem sigmaOf_mul {R : Ranks} (H : Host R) (g g' : R.GG) :
    H.sigmaOf (g * g') = H.sigmaOf g * H.sigmaOf g' := map_mul (H.gal).symm g g'

theorem sigmaOf_one {R : Ranks} (H : Host R) : H.sigmaOf 1 = 1 := map_one (H.gal).symm

theorem emb_apply {R : Ranks} (H : Host R) (g : R.GG) (x : H.E) : H.emb g x = H.φ₀ (H.sigmaOf g x) := rfl

def galK {R : Ranks} (H : Host R) (g : R.Psi) : H.E ≃ₐ[H.K] H.E :=
  { (H.sigmaOf g : H.E ≃+* H.E) with
    commutes' := fun a => sigmaOf_fix_K H g g.2 a a.2 }

theorem galK_apply {R : Ranks} (H : Host R) (g : R.Psi) (x : H.E) : galK H g x = H.sigmaOf g x := rfl

theorem galK_bijective {R : Ranks} (H : Host R) : Function.Bijective (galK H) := by
  constructor
  · intro g g' h
    apply Subtype.ext
    apply (H.gal).symm.injective
    exact AlgEquiv.ext fun x => congrArg (fun f : H.E ≃ₐ[H.K] H.E => f x) h
  · intro s
    refine ⟨⟨H.galE (s.restrictScalars ℚ), ?_⟩, ?_⟩
    · rw [H.galE_mem_Psi_iff]
      exact s.commutes ⟨_, bE_mem H⟩
    · refine AlgEquiv.ext fun x => ?_
      rw [galK_apply, sigmaOf_galE]
      rfl

theorem restrict_K (D : D7) : GL3Theta.InducedCMType D := fun τ a => by
  change D.host.φ₀ (D.host.sigmaOf _ _) = _
  rw [sigmaOf_fix_K D.host _ (D.eTau τ).2 _ a.2]

theorem sum_eq_trace (D : D7) : TraceMapNormalisation D := fun y => by
  have hE := D.host.hostE_isGalois
  have h := trace_eq_sum_automorphisms (K := D.host.K) (L := D.host.E) y
  change _ = D.host.φ₀ (algebraMap D.host.K D.host.E _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  exact Fintype.sum_bijective (galK D.host ∘ D.eTau) ((galK_bijective D.host).comp D.eTau.bijective) _ _
    (fun τ => rfl)

theorem permutes (D : D7) : EmbeddingPermutesTypes D := fun M ρ hK hM => by
  have h0 : ∀ x, D.host.φ₀ x ∈ M := fun x => by
    have := hM (D.eTau.symm 1) x
    rwa [embT, Equiv.apply_symm_apply, emb_apply, Subgroup.coe_one, sigmaOf_one] at this
  let ψ : D.host.E →+* ℂ := (ρ : M →+* ℂ).comp (D.host.φ₀.codRestrict M h0)
  have hψ : ∀ x, cj M ρ (D.host.φ₀ x) = ψ x := fun x => by
    rw [cj, TaylorLogMetric.liftM, dite_eq_left (h0 x)]
    rfl
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ψ
  have hgP : g ∈ D.R.Psi := by
    rw [← galE_sigmaOf D.host g, D.host.galE_mem_Psi_iff]
    apply D.host.φ₀.injective
    rw [← emb_apply, hg, ← hψ]
    exact (hK ⟨_, bE_mem D.host⟩).2
  refine ⟨D.eTau.trans ((Equiv.mulLeft (⟨g, hgP⟩ : D.R.Psi)).trans D.eTau.symm), fun τ x => ?_⟩
  rw [embT, emb_apply, hψ, ← hg, embT, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.coe_mulLeft, Subgroup.coe_mul, emb_apply, emb_apply, sigmaOf_mul]
  rfl

theorem induced_type : ∀ D : D7, admG1 D ∧ EmbeddingPermutesTypes D :=
  fun D => ⟨⟨restrict_K D, sum_eq_trace D⟩, permutes D⟩

end GlobalTheory.InducedType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InjAndRatOfLi
section
set_option autoImplicit false

noncomputable section

open Formalism.IndefR.Bridge Formalism.L2.DIV NumberField GlobalTheory.PresBasic

namespace GlobalTheory.TraceIncl

section Scalar

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}

theorem exists_int_smul (f : V →ₛₗ[σ] W) (hinj : Function.Injective f)
    (hs : ∀ x y (c : ℂ), f x = c • f y → y = 0 ∨ ∃ a, σ a = c) {x y : V} {c : ℂˣ} (hc : IsOfFinOrder c)
    (h : f x = (c : ℂ) • f y) : ∃ a : 𝓞 K, x = (a : K) • y := by
  rcases hs x y c h with rfl | ⟨a, ha⟩
  · exact ⟨0, hinj (by rw [h]; simp)⟩
  · obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
    have h1 : a ^ n = 1 := σ.injective (by rw [map_pow, ha, ← Units.val_pow_eq_pow_val, e, Units.val_one, map_one])
    refine ⟨⟨a, IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)⟩, hinj ?_⟩
    rw [h, map_smulₛₗ, ← ha]
    rfl

theorem inj_and_rat_of_li (f : V →ₛₗ[σ] W)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => f (b k)) :
    Function.Injective f ∧ ∀ x y (c : ℂ), f x = c • f y → y = 0 ∨ ∃ a, σ a = c := by
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    by_contra h0
    have := (hli 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0
    exact this hx
  refine ⟨hinj, fun x y c h => ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  have hy' : f y ≠ 0 := fun h0 => hy (hinj (by rw [h0, map_zero]))
  by_cases hl : LinearIndependent K ![y, x]
  · have h2 : LinearIndependent ℂ ![f y, f x] := by
      convert hli 2 _ hl using 1
      funext k
      fin_cases k <;> rfl
    exact absurd h.symm ((LinearIndependent.pair_iff' hy').1 h2 c)
  · rw [LinearIndependent.pair_iff' hy] at hl
    push Not at hl
    obtain ⟨a, rfl⟩ := hl
    rw [map_smulₛₗ] at h
    exact Or.inr ⟨a, smul_left_injective ℂ hy' h⟩

end Scalar

variable {G Γ W K X : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] [AddCommGroup X] [Module ℂ X] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ) (k : G → W →ₗ[ℂ] X)

theorem coef_rat (x y : S.V) (c : ℂ) (h : P.coef x = c • P.coef y) : y = 0 ∨ ∃ a, σ a = c := by
  by_cases hy : y = 0
  · exact Or.inl hy
  obtain ⟨j, hj⟩ : ∃ j, S.bV.repr y j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hy (S.bV.repr.injective (by ext j; simp [hn j]))
  have e := congrArg (fun w => (bW P).repr w j) h
  simp only [map_smul, Finsupp.smul_apply, repr_coef, smul_eq_mul] at e
  refine Or.inr ⟨S.bV.repr x j / S.bV.repr y j, ?_⟩
  rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hj)]

theorem card_stab (γ : Γ) (y : G) (j : J) : Nat.card (stab ι J (ι γ * y * j)) = Nat.card (stab ι J y) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj γ⁻¹).toEquiv fun δ => ?_)
  rw [mem_stab, mem_stab]
  have e : (ι γ * y * j)⁻¹ * ι δ * (ι γ * y * j) = (j : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * j := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right j.2, J.mul_mem_cancel_left (J.inv_mem j.2)]

theorem sum_translate (κ : G) (h1 : ∀ j ∈ J, κ * j * κ⁻¹ ∈ J) (h2 : ∀ j ∈ J, κ⁻¹ * j * κ ∈ J) (Φ : G → X)
    (hΦ : ∀ γ h (j : J), Φ (ι γ * h * j) = Φ h) :
    ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • Φ (P.y c * κ) = ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • Φ (P.y c) := by
  have hinj : Function.Injective fun c => P.decC (P.y c * κ) := by
    intro c c' e
    have e1 := P.dec_spec (P.y c * κ)
    have e2 := P.dec_spec (P.y c' * κ)
    simp only at e
    rw [← e] at e2
    generalize P.decC (P.y c * κ) = d at e1 e2
    generalize P.decG (P.y c * κ) = γ at e1
    generalize P.decK (P.y c * κ) = j at e1
    generalize P.decG (P.y c' * κ) = γ' at e2
    generalize P.decK (P.y c' * κ) = j' at e2
    refine (P.reps (P.y c')).unique ⟨γ' * γ⁻¹, ⟨_, h1 _ (j⁻¹ * j').2⟩, ?_⟩ ⟨1, 1, by simp⟩
    rw [eq_mul_inv_of_mul_eq e1, eq_mul_inv_of_mul_eq e2]
    simp [mul_assoc]
  refine Fintype.sum_bijective _ (Finite.injective_iff_bijective.1 hinj) _ _ fun c => ?_
  have e1 := P.dec_spec (P.y c * κ)
  have e2 : stab ι J (P.y c * κ) = stab ι J (P.y c) := by
    ext δ
    rw [mem_stab, mem_stab]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · convert h1 _ h using 1
      group
    · convert h2 _ h using 1
      group
  rw [← e2]
  conv_lhs => rw [e1, card_stab, hΦ]

def clSum : S.Forms →ₛₗ[σ] X where
  toFun f := ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • k (P.y c) (P.extL f (P.y c))
  map_add' f f' := by simp [Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [map_smulₛₗ, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _

theorem clSum_apply (f : S.Forms) :
    clSum P k f = ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • k (P.y c) (P.coef ((f : S.Cl → S.V) c)) :=
  Finset.sum_congr rfl fun c _ => by rw [ClassPres.extL_apply, ext_y]

structure KernelLaws (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) {J : Subgroup G} (χ : J →* ℂˣ) (k : G → W →ₗ[ℂ] X) : Prop where
  aut : ∀ γ h w, k (ι γ * h) (ρ γ w) = k h w
  typ : ∀ h (j : J) w, k (h * j) w = (((χ j)⁻¹ : ℂˣ) : ℂ) • k h w

variable {k}

theorem KernelLaws.dec (hk : KernelLaws ι ρ χ k) (γ : Γ) (h : G) (j : J) (w : W) :
    (χ j : ℂ) • k (ι γ * h * j) (ρ γ w) = k h w := by
  rw [hk.typ, hk.aut, smul_smul, Units.mul_inv, one_smul]

theorem KernelLaws.form (hk : KernelLaws ι ρ χ k) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) (γ : Γ) (h : G) (j : J) :
    k (ι γ * h * j) (F (ι γ * h * j)) = k h (F h) := by
  rw [hF γ h j, map_smul, hk.dec]

theorem clSum_avgForm (hk : KernelLaws ι ρ χ k) (c : S.Cl) (x : S.V) :
    clSum P k (avgForm S c x) = k (P.y c) (P.coef x) := by
  classical
  rw [clSum_apply, Finset.sum_eq_single c]
  · have hg : ∀ g : S.Gam c, k (P.y c) (P.coef (S.ρ c g x)) = k (P.y c) (P.coef x) := fun g => by
      have := hk.dec (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g)) (P.coef x)
      rwa [stabK_spec, ← map_smul, ← P.coef_act] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [avgForm, Pi.single_eq_same, map_sum, hg, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  · intro c' _ hc
    simp [avgForm, Pi.single_eq_of_ne hc]
  · simp

theorem clSum_act (hk : KernelLaws ι ρ χ k) {Q : Subgroup G} {ch : Q →* ℂˣ} {G0 : Type} [Group G0]
    {act : Representation K G0 S.Forms} (T : ActTie ι P Q ch act) (hJ : J ≤ Q) (a : G0 → X →ₗ[ℂ] X)
    (ha : ∀ (q : Q) h w, a (T.red q) (k (h * q) w) = (((ch q)⁻¹ : ℂˣ) : ℂ) • k h w) (g : G0) (f : S.Forms) :
    clSum P k (act g f) = a g (clSum P k f) := by
  obtain ⟨q, rfl⟩ := T.red_surj g
  have hn : ∀ (q : Q), ∀ j ∈ J, (q : G) * j * (q : G)⁻¹ ∈ J := fun q j hj =>
    (T.red_ker (q * ⟨j, hJ hj⟩ * q⁻¹)).1 (by
      rw [map_mul, map_mul, (T.red_ker ⟨j, hJ hj⟩).2 hj, mul_one, ← map_mul, mul_inv_cancel, map_one])
  have key := sum_translate P (q : G) (hn q) (fun j hj => by simpa using hn q⁻¹ j hj)
    (fun h => k h (P.ext f h)) (hk.form (extMem P f))
  change ∑ c, _ • k (P.y c) (P.ext _ (P.y c)) = a _ (∑ c, _ • k (P.y c) (P.ext _ (P.y c)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← key, map_sum, T.act_eq _ q rfl]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ha, g0Act, map_smul]

structure LatSys (r : Γ → S.V →ₗ[K] S.V) (L : G → Submodule (𝓞 K) S.V) : Prop where
  coef : ∀ γ x, P.coef (r γ x) = ρ γ (P.coef x)
  move : ∀ γ h (j : J), ∀ x ∈ L h, r γ x ∈ L (ι γ * h * j)
  nab : ∀ c, L (P.y c) = S.Nab c

variable {P} {r : Γ → S.V →ₗ[K] S.V} {L : G → Submodule (𝓞 K) S.V}

theorem LatSys.avg_mem (hL : LatSys P r L) (hχ : ∀ j, IsOfFinOrder (χ j)) {c : S.Cl} {x : S.V} (hx : x ∈ S.Nab c) (c' : S.Cl) :
    (avgForm S c x : S.Cl → S.V) c' ∈ S.Nab c' := by
  classical
  by_cases h : c' = c
  · subst h
    simp only [avgForm, Pi.single_eq_same]
    refine Submodule.sum_mem _ fun g _ => ?_
    have h1 := hL.move (P.stabI c' g : Γ) (P.y c') (stabK ι (P.stabI c' g)) x (hL.nab c' ▸ hx)
    rw [stabK_spec, hL.nab] at h1
    obtain ⟨a, ha⟩ := exists_int_smul P.coef (coef_injective P) (coef_rat P) (hχ _)
      ((P.coef_act c' g x).trans (by rw [← hL.coef]))
    rw [ha]
    have h2 := Submodule.smul_mem _ a h1
    rwa [← algebraMap_smul K a] at h2
  · simp [avgForm, Pi.single_eq_of_ne h]

theorem LatSys.exists_trace (hL : LatSys P r L) (hχ : ∀ j, IsOfFinOrder (χ j)) (hk : KernelLaws ι ρ χ k) {h : G} {x : S.V}
    (hx : x ∈ L h) : ∃ f : S.Forms, (∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) ∧
      ∃ j : J, k h (P.coef x) = (((χ j)⁻¹ : ℂˣ) : ℂ) • clSum P k f := by
  obtain ⟨c, ⟨γ, j, rfl⟩, -⟩ := P.reps h
  have h1 := hL.move γ⁻¹ _ j⁻¹ x hx
  rw [show ι γ⁻¹ * (ι γ * P.y c * j) * (j⁻¹ : J) = P.y c by simp [mul_assoc], hL.nab] at h1
  refine ⟨avgForm S c (r γ⁻¹ x), hL.avg_mem hχ h1, j, ?_⟩
  rw [clSum_avgForm P hk, ← hk.dec γ (P.y c) j, smul_smul, Units.inv_mul, one_smul, hL.coef, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.TraceIncl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalBasisGaloisMap
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem aut_conj_comm (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (x : D.host.E) :
    σ (D.host.conj x) = D.host.conj (σ x) := by
  have h : σ * D.host.conj = D.host.conj * σ :=
    (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg (fun f : D.host.E ≃ₐ[ℚ] D.host.E => f x) h

theorem hYY_map_aut (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : ∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E))
    {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (x.map σ) (y.map σ) = hYY D x y := by
  let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
  unfold hYY
  rw [← Algebra.trace_eq_of_algEquiv e (∑ i, ∑ j, x i j * D.host.conj (y i j))]
  congr 1
  show _ = σ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Matrix.map_apply, aut_conj_comm]

theorem onB_map_aut : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) →
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  intro D σ hσ N N' r b hb
  refine ⟨?_, ?_⟩
  · intro i j
    rw [hYY_map_aut D σ hσ]
    exact hb.1 i j
  · let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
    let L : Matrix (Fin N') (Fin N) D.host.E ≃ₗ[D.host.K] Matrix (Fin N') (Fin N) D.host.E :=
      e.toLinearEquiv.mapMatrix
    have h : (fun j => (b j).map σ) = L.toLinearMap ∘ b := rfl
    rw [h, Set.range_comp, ← Submodule.map_span, hb.2, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.NormSum
end

