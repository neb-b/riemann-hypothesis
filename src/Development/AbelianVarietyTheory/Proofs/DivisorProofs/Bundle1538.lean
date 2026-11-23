module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdSumFixEig
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.StdSumFix

variable {D : D7}

theorem hatId_mul_left {𝔪 : Ideal (𝓞 D.host.E)} {t y : AE D} (ht : t ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    t * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, t * s, mul_mem ht hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

abbrev mat {N : ℕ} (k : GA D N) : Matrix (Fin N) (Fin N) (AE D) := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))

theorem mat_mul {N : ℕ} (x y : GA D N) : mat (x * y) = mat x * mat y := rfl

theorem mat_inv_mul {N : ℕ} (x : GA D N) : mat x⁻¹ * mat x = 1 := by
  simp [mat]

theorem mat_mul_inv {N : ℕ} (x : GA D N) : mat x * mat x⁻¹ = 1 := by
  simp [mat]

theorem ent_mul_left {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (hB : ∀ i j, B i j ∈ hatId D 𝔪) (i j : Fin N) : (A * B) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => hatId_mul_left (hA i l) (hB l j)

theorem ent_mul_right {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hB : ∀ i j, B i j ∈ hatId D 𝔪) (hA : ∀ i j, A i j ∈ OhE D) (i j : Fin N) : (B * A) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => by rw [mul_comm]; exact hatId_mul_left (hA l j) (hB i l)

theorem ent_of_mem {N : ℕ} {k : GA D N} (hk : k ∈ intG D N) (i j : Fin N) : mat k i j ∈ OhE D :=
  ((mem_intG k).1 hk i j).1

theorem ent_inv_of_mem {N : ℕ} {k : GA D N} (hk : k ∈ intG D N) (i j : Fin N) : mat k⁻¹ i j ∈ OhE D :=
  ((mem_intG k⁻¹).1 (inv_mem hk) i j).1

variable {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ}

theorem congOne_one : CongOne D 𝔪 (1 : GA D N) := fun i j => by
  simp only [OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply]; exact zero_mem _

theorem congOne_mul {x y : GA D N} (hx : x ∈ intG D N) (cx : CongOne D 𝔪 x) (cy : CongOne D 𝔪 y) :
    CongOne D 𝔪 (x * y) := fun i j => by
  have e : mat (x * y) - 1 = mat x * (mat y - 1) + (mat x - 1) := by rw [mat_mul, mul_sub, mul_one]; abel
  change (mat (x * y) - 1) i j ∈ _
  rw [e, Matrix.add_apply]
  exact add_mem (ent_mul_left (ent_of_mem hx) cy i j) (cx i j)

theorem congOne_inv {x : GA D N} (hx : x ∈ intG D N) (cx : CongOne D 𝔪 x) : CongOne D 𝔪 x⁻¹ := fun i j => by
  have e : mat x⁻¹ - 1 = -(mat x⁻¹ * (mat x - 1)) := by rw [mul_sub, mat_inv_mul, mul_one]; abel
  change (mat x⁻¹ - 1) i j ∈ _
  rw [e, Matrix.neg_apply]
  exact neg_mem (ent_mul_left (ent_inv_of_mem hx) cx i j)

theorem congOne_conj {g x : GA D N} (hg : g ∈ intG D N) (cx : CongOne D 𝔪 x) : CongOne D 𝔪 (g * x * g⁻¹) :=
  fun i j => by
  have e : mat (g * x * g⁻¹) - 1 = mat g * (mat x - 1) * mat g⁻¹ := by
    rw [mat_mul, mat_mul, mul_sub, sub_mul, mul_one, mat_mul_inv]
  change (mat (g * x * g⁻¹) - 1) i j ∈ _
  rw [e]
  exact ent_mul_right (ent_mul_left (ent_of_mem hg) cx) (ent_inv_of_mem hg) i j

end GlobalTheory.StdSumFix

namespace GlobalTheory.StdSumFix

variable {D : D7}

theorem zero_mem_TT (T : Tor D) (N N' : ℕ) : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

theorem add_mem_TT {T : Tor D} {N N' : ℕ} {F G : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hG : G ∈ TT D T N N') :
    F + G ∈ TT D T N N' := by
  obtain ⟨hF1, m, hm, hFm⟩ := hF
  obtain ⟨hG1, n, hn, hGn⟩ := hG
  refine ⟨hF1.add hG1, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
  have h1 := hFm (n • x) (AddSubgroup.nsmul_mem _ hx n)
  have h2 := hGn (m • x) (AddSubgroup.nsmul_mem _ hx m)
  rw [smul_smul] at h1 h2
  rw [mul_comm n m] at h2
  funext z
  have e1 := congrFun h1 z
  have e2 := congrFun h2 z
  simp only [Wd, U, Pi.add_apply] at e1 e2 ⊢
  linear_combination e1 + e2

theorem Om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {ι : Type*} (s : Finset ι) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i ∈ s, f i ∈ TT D (tor0 D cc δ) N N') :
    (∑ i ∈ s, f i) ∈ TT D (tor0 D cc δ) N N' ∧ W.Om g g' (∑ i ∈ s, f i) = ∑ i ∈ s, W.Om g g' (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using zero_mem_TT (tor0 D cc δ) N N', ?_⟩
    have h := W.smul g g' 0 0 (zero_mem_TT _ N N')
    simpa using h
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hfi := hf i (Finset.mem_insert_self i s)
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact ⟨add_mem_TT hfi h1, by rw [W.add g g' _ hfi _ h1, h2]⟩

end GlobalTheory.StdSumFix

namespace GlobalTheory.StdSumFix

variable {D : D7}

section Reps

variable {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) {𝔪 : Ideal (𝓞 D.host.E)}
  {v : VC D a d → ℂ} {R : Finset (GA D a)}

theorem Om_rep (hv : v ∈ TT D (tor0 D ⊤ δ) a d) (hfix : ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v)
    {x r : GA D a} (hx : x ∈ intG D a) (hr : r ∈ intG D a) (hc : CongOne D 𝔪 (r⁻¹ * x)) :
    W.Om x 1 v = W.Om r 1 v := by
  have h := W.mul r (r⁻¹ * x) 1 1 v hv
  rw [mul_inv_cancel_left, mul_one] at h
  rw [h, hfix _ (mul_mem (inv_mem hr) hx) hc]

theorem sum_reindex (hv : v ∈ TT D (tor0 D ⊤ δ) a d) (hfix : ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v)
    (hRi : ∀ r ∈ R, r ∈ intG D a) (hR : ∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k))
    (φ : GA D a → GA D a) (hφ : ∀ r ∈ R, φ r ∈ intG D a)
    (inj : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s ∈ R, CongOne D 𝔪 (s⁻¹ * φ r₁) → CongOne D 𝔪 (s⁻¹ * φ r₂) → r₁ = r₂)
    (surj : ∀ s ∈ R, ∃ r ∈ R, CongOne D 𝔪 (s⁻¹ * φ r)) :
    ∑ r ∈ R, W.Om (φ r) 1 v = ∑ s ∈ R, W.Om s 1 v := by
  classical
  let ψ : GA D a → GA D a := fun r => if h : r ∈ R then (hR (φ r) (hφ r h)).exists.choose else r
  have hψ : ∀ r ∈ R, ψ r ∈ R ∧ CongOne D 𝔪 ((ψ r)⁻¹ * φ r) := fun r hr => by
    simp only [ψ, dif_pos hr]; exact (hR (φ r) (hφ r hr)).exists.choose_spec
  refine Finset.sum_nbij ψ (fun r hr => (hψ r hr).1) ?_ ?_ ?_
  · intro r₁ hr₁ r₂ hr₂ e
    have h1 := (hψ r₁ hr₁).2
    have h2 := (hψ r₂ hr₂).2
    rw [e] at h1
    exact inj r₁ hr₁ r₂ hr₂ (ψ r₂) (hψ r₂ hr₂).1 h1 h2
  · intro s hs
    obtain ⟨r, hr, hc⟩ := surj s hs
    exact ⟨r, hr, (hR (φ r) (hφ r hr)).unique (hψ r hr) ⟨hs, hc⟩⟩
  · intro r hr
    exact Om_rep W hv hfix (hφ r hr) (hRi _ (hψ r hr).1) (hψ r hr).2

end Reps

theorem stdSum_fix_eig : ∀ (D : D7) (δ : ℂ) (a d : ℕ) (e0 : VC D a d → ℂ) (W : WeilO D ⊤ δ a d e0)
    (𝔪 : Ideal (𝓞 D.host.E)) (v : VC D a d → ℂ), v ∈ TT D (tor0 D ⊤ δ) a d →
    (∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) →
    (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (∀ k ∈ intG D a, W.Om k 1 (∑ r ∈ R, W.Om r 1 v) = ∑ r ∈ R, W.Om r 1 v) ∧
    ∀ (j : GA D d) (k : GA D a) (c : ℂ), k ∈ intG D a → W.Om 1 j v = c • W.Om k 1 v →
      W.Om 1 j (∑ r ∈ R, W.Om r 1 v) = c • ∑ r ∈ R, W.Om r 1 v := by
  intro D δ a d e0 W 𝔪 v hv hfix R hRi hR
  have hTT : ∀ r ∈ R, W.Om r 1 v ∈ TT D (tor0 D ⊤ δ) a d := fun r _ => W.maps r 1 v hv
  have uniq : ∀ r₁ ∈ R, ∀ r₂ ∈ R, CongOne D 𝔪 (r₁⁻¹ * r₂) → r₁ = r₂ := fun r₁ h₁ r₂ h₂ hc =>
    (hR r₂ (hRi r₂ h₂)).unique ⟨h₁, hc⟩ ⟨h₂, by rw [inv_mul_cancel]; exact congOne_one⟩
  refine ⟨fun k hk => ?_, fun j k c hk hj => ?_⟩
  · rw [(Om_sum W k 1 R _ hTT).2]
    have e : ∀ r ∈ R, W.Om k 1 (W.Om r 1 v) = W.Om (k * r) 1 v := fun r _ => by
      rw [← W.mul k r 1 1 v hv, mul_one]
    rw [Finset.sum_congr rfl e]
    refine sum_reindex W hv hfix hRi hR (fun r => k * r) (fun r hr => mul_mem hk (hRi r hr)) ?_ ?_
    · intro r₁ h₁ r₂ h₂ s hs c₁ c₂
      have hm : s⁻¹ * (k * r₁) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem hk (hRi r₁ h₁))
      have h := congOne_mul (inv_mem hm) (congOne_inv hm c₁) c₂
      have e' : (s⁻¹ * (k * r₁))⁻¹ * (s⁻¹ * (k * r₂)) = r₁⁻¹ * r₂ := by group
      rw [e'] at h
      exact uniq r₁ h₁ r₂ h₂ h
    · intro s hs
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hR (k⁻¹ * s) (mul_mem (inv_mem hk) (hRi s hs))
      refine ⟨r, hr, ?_⟩
      have h := congOne_inv (mul_mem (inv_mem (hRi r hr)) (mul_mem (inv_mem hk) (hRi s hs))) hc
      have e' : (r⁻¹ * (k⁻¹ * s))⁻¹ = s⁻¹ * (k * r) := by group
      rwa [e'] at h
  · rw [(Om_sum W 1 j R _ hTT).2]
    have e : ∀ r ∈ R, W.Om 1 j (W.Om r 1 v) = c • W.Om (r * k) 1 v := fun r _ => by
      rw [← W.mul 1 r j 1 v hv, one_mul, mul_one,
        show W.Om r j v = W.Om (r * 1) (1 * j) v by rw [mul_one, one_mul], W.mul r 1 1 j v hv, hj,
        W.smul r 1 c _ (W.maps k 1 v hv), ← W.mul r k 1 1 v hv, mul_one]
    rw [Finset.sum_congr rfl e, ← Finset.smul_sum]
    congr 1
    refine sum_reindex W hv hfix hRi hR (fun r => r * k) (fun r hr => mul_mem (hRi r hr) hk) ?_ ?_
    · intro r₁ h₁ r₂ h₂ s hs c₁ c₂
      have hm₂ : s⁻¹ * (r₂ * k) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem (hRi r₂ h₂) hk)
      have hm₁ : s⁻¹ * (r₁ * k) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem (hRi r₁ h₁) hk)
      have h := congOne_conj (g := r₂⁻¹ * s) (mul_mem (inv_mem (hRi r₂ h₂)) (hRi s hs))
        (congOne_mul hm₁ c₁ (congOne_inv hm₂ c₂))
      have e' : r₂⁻¹ * s * (s⁻¹ * (r₁ * k) * (s⁻¹ * (r₂ * k))⁻¹) * (r₂⁻¹ * s)⁻¹ = r₂⁻¹ * r₁ := by group
      rw [e'] at h
      exact (uniq r₂ h₂ r₁ h₁ h).symm
    · intro s hs
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hR (s * k⁻¹) (mul_mem (hRi s hs) (inv_mem hk))
      refine ⟨r, hr, ?_⟩
      have hm : r⁻¹ * (s * k⁻¹) ∈ intG D a := mul_mem (inv_mem (hRi r hr)) (mul_mem (hRi s hs) (inv_mem hk))
      have h := congOne_conj (g := k⁻¹) (inv_mem hk) (congOne_inv hm hc)
      have e' : k⁻¹ * (r⁻¹ * (s * k⁻¹))⁻¹ * k⁻¹⁻¹ = s⁻¹ * (r * k) := by group
      rwa [e'] at h

end GlobalTheory.StdSumFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormSqLeOfRootOfUnityAddCharCombination
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ParsevalRootsOfUnity

theorem isIntegral_of_pow_eq_one {R : Type} [CommRing R] (z : R) (m : ℕ) (hm : 0 < m)
    (h : z ^ m = 1) : IsIntegral ℤ z :=
  ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [h]⟩

theorem mem_Qbar_of_pow_eq_one (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : z ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact ((isIntegral_of_pow_eq_one z m hm h).tower_top (A := ℚ)).isAlgebraic

theorem norm_eq_one_of_pow_eq_one' (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : ‖z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg z) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity : ∀ {ι Q : Type} [Fintype ι] [Fintype Q] [AddCommGroup Q] (N k : ℕ) (c : ι → ℂ) (χ : ι → AddChar Q ℂ), 0 < N → (∀ i, ∃ m : ℕ, 0 < m ∧ c i ^ m = 1) → Function.Injective χ → Fintype.card Q = N ^ k → Fintype.card ι ≤ N ^ k → ∃ r : Q → Qbar, (∀ q, (r q : ℂ) = ((N : ℂ) ^ k)⁻¹ * ∑ i, c i * χ i q) ∧ (∀ q, IsIntegral ℤ ((N : Qbar) ^ k * r q)) ∧ ∀ ρ : Qbar →+* ℂ, (∑ q, ‖ρ (r q)‖) ^ 2 ≤ (N : ℝ) ^ k := by
  intro ι Q _ _ _ N k c χ hN hc hχ hQ hι
  classical
  choose m hm hcm using hc
  have hQpos : 0 < Fintype.card Q := Fintype.card_pos
  have hχq : ∀ i q, χ i q ^ Fintype.card Q = 1 := fun i q => by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  let cq : ι → Qbar := fun i => ⟨c i, mem_Qbar_of_pow_eq_one _ _ (hm i) (hcm i)⟩
  let xq : ι → Q → Qbar := fun i q => ⟨χ i q, mem_Qbar_of_pow_eq_one _ _ hQpos (hχq i q)⟩
  have hNQ : (N : Qbar) ≠ 0 := by exact_mod_cast hN.ne'
  let r : Q → Qbar := fun q => ((N : Qbar) ^ k)⁻¹ * ∑ i, cq i * xq i q
  refine ⟨r, ?_, ?_, ?_⟩
  · intro q
    simp [r, cq, xq]
  · intro q
    have : (N : Qbar) ^ k * r q = ∑ i, cq i * xq i q := by
      simp only [r]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hNQ), one_mul]
    rw [this]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
    · exact isIntegral_of_pow_eq_one _ (m i) (hm i) (Subtype.ext (by simpa [cq] using hcm i))
    · exact isIntegral_of_pow_eq_one _ _ hQpos (Subtype.ext (by simpa [xq] using hχq i q))
  · intro ρ
    let χ' : ι → AddChar Q Qbar := fun i =>
      { toFun := xq i
        map_zero_eq_one' := Subtype.ext (by simp [xq])
        map_add_eq_mul' := fun a b => Subtype.ext (by simp [xq, AddChar.map_add_eq_mul]) }
    let ψ : ι → AddChar Q ℂ := fun i => (ρ : Qbar →* ℂ).compAddChar (χ' i)
    have hψ : ∀ i q, ψ i q = ρ (xq i q) := fun i q => rfl
    let a : ι → ℂ := fun i => ρ (cq i)
    have ha : ∀ i, a i * (starRingEnd ℂ) (a i) = 1 := by
      intro i
      have h1 : a i ^ m i = 1 := by
        simp only [a]
        rw [← map_pow]
        have : cq i ^ m i = 1 := Subtype.ext (by simpa [cq] using hcm i)
        rw [this, map_one]
      rw [Complex.mul_conj', norm_eq_one_of_pow_eq_one' _ _ (hm i) h1]
      simp
    have hinj : Function.Injective ψ := by
      intro i j hij
      apply hχ
      ext q
      have h1 : ρ (xq i q) = ρ (xq j q) := by rw [← hψ, ← hψ, hij]
      have h2 := congrArg Subtype.val (ρ.injective h1)
      simpa [xq] using h2
    have horth : ∀ i j, ∑ q, ψ i q * (starRingEnd ℂ) (ψ j q) = if i = j then (Fintype.card Q : ℂ) else 0 := by
      intro i j
      have : ∀ q, ψ i q * (starRingEnd ℂ) (ψ j q) = (ψ i - ψ j) q := fun q => by
        rw [AddChar.sub_apply, AddChar.map_neg_eq_conj]
      simp_rw [this]
      rw [AddChar.sum_eq_ite]
      by_cases h : i = j
      · simp [h]
      · have : ψ i - ψ j ≠ 0 := fun h' => h (hinj (sub_eq_zero.1 h'))
        simp [h, this]
    let f : Q → ℂ := fun q => ∑ i, a i * ψ i q
    have hpars : ∑ q, ‖f q‖ ^ 2 = (Fintype.card Q : ℝ) * Fintype.card ι := by
      apply Complex.ofReal_injective
      push_cast
      simp_rw [← Complex.mul_conj']
      calc ∑ q, f q * (starRingEnd ℂ) (f q)
          = ∑ q, ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [f, map_sum, map_mul, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * ∑ q, (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            simp [Finset.mul_sum]
        _ = ∑ i, (Fintype.card Q : ℂ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [horth, ha]
        _ = (Fintype.card Q : ℂ) * Fintype.card ι := by
            simp [mul_comm]
    have hCS : (∑ q, ‖f q‖) ^ 2 ≤ (Fintype.card Q : ℝ) * ∑ q, ‖f q‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Q)) (f := fun q => ‖f q‖)
      simpa using this
    have hρr : ∀ q, ‖ρ (r q)‖ = ((N : ℝ) ^ k)⁻¹ * ‖f q‖ := by
      intro q
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [r, map_mul, map_inv₀, map_pow, map_natCast, map_sum, norm_mul, norm_inv,
        norm_pow, Complex.norm_natCast, f, a, hψ]
    simp_rw [hρr]
    rw [← Finset.mul_sum, mul_pow]
    have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
    have hQr : (Fintype.card Q : ℝ) = (N : ℝ) ^ k := by exact_mod_cast hQ
    have hιr : (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ k := by exact_mod_cast hι
    calc (((N : ℝ) ^ k)⁻¹) ^ 2 * (∑ q, ‖f q‖) ^ 2
        ≤ (((N : ℝ) ^ k)⁻¹) ^ 2 * ((Fintype.card Q : ℝ) * ((Fintype.card Q : ℝ) * (Fintype.card ι : ℝ))) := by
          gcongr
          rw [← hpars]; exact hCS
      _ = (Fintype.card ι : ℝ) := by
          rw [hQr]; field_simp
      _ ≤ (N : ℝ) ^ k := hιr

end GlobalTheory.ParsevalRootsOfUnity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAdd
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LamSpread


open Classical in
def sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (b : E →+* ℂ) : ℕ := ∑ i : Fin (Dw.mult b), a (b, i)

theorem le_sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (b : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult b) : a (b, i) ≤ sumA Dw a b :=
  Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => a (b, i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨i, hi⟩ : Fin (Dw.mult b)))

theorem spread_le_sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 0 < r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (k : U.Comp) (τ : (U.X k).Ψ) :
    (U.X k).spread (laU U a n k) τ ≤ (sumA Dw a (Function.invFun (relab c σ) τ.1) : ℝ) +
      sumA Dw a (Function.invFun (relab c σ) (conjEmb τ.1)) + n := by
  have hsurj : Function.Surjective (relab (E := E) c σ) :=
    Finite.injective_iff_surjective.1 (GlobalTheory.AllWt.relab_injective σ)
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hrr := hU.1
  obtain ⟨ρ, hρ⟩ := hsurj τ.1
  have hρΨ : ρ (H.rt : E) = H.rt0 := by
    by_contra hn
    have h3 : relab c σ (conjEmb ρ) (H.rt : E) = H.rt0 := by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext (GlobalTheory.AllWt.conj_mem hn))).trans hσ0
    rw [GlobalTheory.AllWt.relab_conj, hρ] at h3
    exact GlobalTheory.AllWt.conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
  have e1 : Function.invFun (relab c σ) τ.1 = ρ := by
    rw [← hρ]; exact Function.leftInverse_invFun (GlobalTheory.AllWt.relab_injective σ) ρ
  have e2 : Function.invFun (relab c σ) (conjEmb τ.1) = conjEmb ρ := by
    rw [← hρ, ← GlobalTheory.AllWt.relab_conj]; exact Function.leftInverse_invFun (GlobalTheory.AllWt.relab_injective σ) _
  have m1 : Dw.mult ρ = Dw.p := by rw [Datum.mult, if_pos hρΨ]
  have m2 : Dw.mult (conjEmb ρ) = Dw.q := by rw [Datum.mult, if_neg (GlobalTheory.AllWt.conj_not_mem ⟨ρ, hρΨ⟩)]
  rw [e1, e2]
  have hn : ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) ≤ n := by
    have : n / 2 + n / 2 ≤ n := by omega
    exact_mod_cast this
  have key : ∀ i : Fin r, -((sumA Dw a (conjEmb ρ) : ℤ) + ((n / 2 : ℕ) : ℤ)) ≤ laU U a n k τ i ∧
      laU U a n k τ i ≤ (sumA Dw a ρ : ℤ) + ((n / 2 : ℕ) : ℤ) := by
    intro i
    have hi' := i.isLt
    unfold laU
    rw [e1, e2]
    split_ifs with hi
    · have := le_sumA Dw a ρ ((i : ℕ) - (U.X k).p0) (by rw [m1]; omega)
      constructor <;> omega
    · have := le_sumA Dw a (conjEmb ρ) ((U.X k).p0 - 1 - (i : ℕ)) (by rw [m2]; omega)
      constructor <;> omega
  refine (GlobalTheory.WtSizes.spread_le hr _ ((sumA Dw a ρ : ℝ) + ((n / 2 : ℕ) : ℝ))
    ((sumA Dw a (conjEmb ρ) : ℝ) + ((n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans (by linarith)
  · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
  · exact_mod_cast (key i).1

theorem sum_spread_laU_le : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : (U σ).Comp), (∑ τ, ((U σ).X k).spread (laU (U σ) a n k) τ) ≤ ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
  intro D j H Dw l Xo c U dict hL σ hσ a n k
  have hU := hL.unf σ hσ
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hsurj : Function.Surjective (relab (E := D.host.E) c σ) :=
    Finite.injective_iff_surjective.1 (GlobalTheory.AllWt.relab_injective σ)
  have hgb : Function.Bijective (Function.invFun (relab c σ)) :=
    Finite.injective_iff_bijective.1 (Function.LeftInverse.injective (Function.rightInverse_invFun hsurj))
  refine (Finset.sum_le_sum fun τ _ => spread_le_sumA (U σ) hσ hU hr a n k τ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (U σ).X k),
    nsmul_eq_mul]
  have h1 : ∑ τ : ((U σ).X k).Ψ, ((sumA Dw a (Function.invFun (relab c σ) τ.1) : ℝ) +
      sumA Dw a (Function.invFun (relab c σ) (conjEmb τ.1))) ≤ absA Dw a := by
    have := GlobalTheory.WtSizes.sum_cm_le ((U σ).X k) (fun b => sumA Dw a (Function.invFun (relab c σ) b))
    rw [hgb.sum_comp (fun b => sumA Dw a b)] at this
    show _ ≤ ((∑ b, sumA Dw a b : ℕ) : ℝ)
    exact_mod_cast this
  have h2 : (fdeg D.host.E : ℝ) * n ≤ ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
    have : fdeg D.host.E * n ≤ fdeg D.host.E * D.R.r * n :=
      Nat.mul_le_mul_right n (Nat.le_mul_of_pos_right _ hr)
    exact_mod_cast this
  linarith

end GlobalTheory.LamSpread
end
end

