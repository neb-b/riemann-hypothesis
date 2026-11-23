module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSlopeMem
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.tangentSlope_mem : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t X Y : ℂ) (u : ℂˣ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → (X - r) / (u : ℂ) ^ 2 ∈ V → (Y - t - s * (X - r)) / (u : ℂ) ^ 3 ∈ V → V.valuation (2 * Y) = V.valuation (u : ℂ) ^ 3 → ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) ∈ V := by
  intro V a₄ a₆ r s t X Y u hI hx hy hv
  obtain ⟨h1, h2, -, h4, -⟩ := hI
  set W' := (⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ) with hW'
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hY : 2 * Y ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact pow_ne_zero 3 ((Valuation.ne_zero_iff _).2 hu) hv.symm
  have hY0 : Y ≠ 0 := right_ne_zero_of_mul hY
  have hq : (u : ℂ) ^ 3 / (2 * Y) ∈ V := by
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, map_pow, ← hv, div_self]
    exact (Valuation.ne_zero_iff _).2 hY
  have hE : 3 * ((X - r) / (u : ℂ) ^ 2) ^ 2 + 2 * W'.a₂ * ((X - r) / (u : ℂ) ^ 2) + W'.a₄
      - W'.a₁ * ((Y - t - s * (X - r)) / (u : ℂ) ^ 3) ∈ V := by
    have h3 : (3 : ℂ) ∈ V := by simpa using natCast_mem V 3
    have h2' : (2 : ℂ) ∈ V := by simpa using natCast_mem V 2
    exact sub_mem (add_mem (add_mem (mul_mem h3 (pow_mem hx 2)) (mul_mem (mul_mem h2' h2) hx)) h4)
      (mul_mem h1 hy)
  have key : ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) =
      (3 * ((X - r) / (u : ℂ) ^ 2) ^ 2 + 2 * W'.a₂ * ((X - r) / (u : ℂ) ^ 2) + W'.a₄
      - W'.a₁ * ((Y - t - s * (X - r)) / (u : ℂ) ^ 3)) * ((u : ℂ) ^ 3 / (2 * Y)) := by
    simp only [hW', WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₄, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [key]
  exact mul_mem hE hq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoCubeMulDerivWeierstrassPNegTwo
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem tendsto_cube_mul_derivWeierstrassP (L : PeriodPair) :
    Filter.Tendsto (fun z : ℂ => z ^ 3 * L.derivWeierstrassP z) (𝓝[≠] 0) (𝓝 (-2)) := by
  have hw : ContinuousAt (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) 0 := by
    have := (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
    fun_prop
  have h1 : Filter.Tendsto (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) (𝓝[≠] 0)
      (𝓝 (-2)) := by
    have := hw.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  have h := L.derivWeierstrassPExcept_sub 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [← h]
  field_simp

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubring
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.TorsMemVal

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact y.2

theorem mem_of_val (V : ValuationSubring ℂ) {n u Ω x : ℂ} (k : ℕ) (hn : V.valuation n = 1)
    (hu : V.valuation u = V.valuation Ω) (h : n ^ k * x / Ω ^ k ∈ V) : x / u ^ k ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_div₀, map_mul, map_pow, map_pow, hn, one_pow, one_mul, ← hu] at h
  rwa [map_div₀, map_pow]

theorem main : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → ∀ z w, z ∉ L.lattice → w ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (N : ℂ) * w ∈ L.lattice → L.derivWeierstrassP z / u ^ 3 ∈ V ∧ (L.weierstrassP z - L.weierstrassP w) / u ^ 2 ∈ V := by
  intro L β u V N hβ hβi hu hN z w hz hw hNz hNw
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (n := 12) (by norm_num)
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hN
    · exact h
  have huΩ : V.valuation u = V.valuation Ω := by
    rw [← hΩ, map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have h := GlobalTheory.WpFam.LatTorsVal.main L β Ω N hβ hβi (hΩ.trans (latticeCurve_Δ L)) hN0
  exact ⟨mem_of_val V 3 hN huΩ (mem_of_isIntegral V (h.1 z hNz).2),
    mem_of_val V 2 hN huΩ (mem_of_isIntegral V (h.2 z w hz hw hNz hNw))⟩

end GlobalTheory.CMModel.TorsMemVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyBoundedSupOfEquicontinuousInvariantTails
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem totallyBounded_sup_of_equicontinuous_tails
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G)
    (Φ : Set (G → ℂ))
    (hinv : ∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g)
    (hbd : ∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B →
      ‖φ (g * u) - φ g‖ ≤ ε)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧
      ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  classical
  intro ε hε
  have hδpos : 0 < ε / 4 := by positivity
  obtain ⟨U, hU, hUeq⟩ := heq (ε / 4) hδpos
  obtain ⟨C, hCc, hCB, hCt⟩ := htail (ε / 4) hδpos
  obtain ⟨t, htC, hCcov⟩ := hCc.elim_nhds_subcover (fun x => (fun h => x⁻¹ * h) ⁻¹' U) (by
    intro x _
    have hc : Continuous (fun h : G => x⁻¹ * h) := continuous_const.mul continuous_id
    apply hc.continuousAt.preimage_mem_nhds
    simpa using hU)
  let T : (G → ℂ) → (t → ℂ) := fun φ i => φ i
  have hTb : T '' Φ ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    exact hbd φ hφ i (hCB (htC i i.2))
  have htb : TotallyBounded (T '' Φ) :=
    ((isCompact_closedBall (0 : t → ℂ) 1).totallyBounded).subset hTb
  obtain ⟨s, hsT, hsf, hscov⟩ := Metric.finite_approx_of_totallyBounded htb (ε / 4) hδpos
  let c : (t → ℂ) → (G → ℂ) := fun y => if h : ∃ φ ∈ Φ, T φ = y then h.choose else 0
  have hc : ∀ y ∈ s, c y ∈ Φ ∧ T (c y) = y := by
    intro y hy
    have h : ∃ φ ∈ Φ, T φ = y := hsT hy
    simp only [c, dif_pos h]
    exact h.choose_spec
  refine ⟨hsf.toFinset.image c, fun φ hφ => ?_⟩
  obtain ⟨y, hy, hdist⟩ : ∃ y ∈ s, dist (T φ) y < ε / 4 := by
    have := hscov ⟨φ, hφ, rfl⟩
    simpa using this
  obtain ⟨hψ, hTψ⟩ := hc y hy
  refine ⟨c y, Finset.mem_image.2 ⟨y, hsf.mem_toFinset.2 hy, rfl⟩, fun g hg => ?_⟩
  rcases hCt g hg with ⟨s', hs', hsg⟩ | hsmall
  · obtain ⟨x, hxt, hxU⟩ : ∃ x ∈ t, x⁻¹ * (s' * g) ∈ U := by
      have := hCcov hsg
      simpa using this
    have hxB : x ∈ B := hCB (htC x hxt)
    have hmul : x * (x⁻¹ * (s' * g)) = s' * g := mul_inv_cancel_left x _
    have hsgB : s' * g ∈ B := hCB hsg
    have h1 := hUeq φ hφ x hxB _ hxU (by rw [hmul]; exact hsgB)
    have h2 := hUeq (c y) hψ x hxB _ hxU (by rw [hmul]; exact hsgB)
    rw [hmul] at h1 h2
    have h3 : ‖φ x - c y x‖ ≤ ε / 4 := by
      calc ‖φ x - c y x‖ = dist (T φ ⟨x, hxt⟩) (T (c y) ⟨x, hxt⟩) := (dist_eq_norm _ _).symm
        _ ≤ dist (T φ) (T (c y)) := dist_le_pi_dist _ _ _
        _ = dist (T φ) y := by rw [hTψ]
        _ ≤ ε / 4 := hdist.le
    rw [← hinv φ hφ s' hs' g, ← hinv (c y) hψ s' hs' g]
    calc ‖φ (s' * g) - c y (s' * g)‖
        = ‖(φ (s' * g) - φ x) + (φ x - c y x) - (c y (s' * g) - c y x)‖ := by congr 1; ring
      _ ≤ ‖φ (s' * g) - φ x‖ + ‖φ x - c y x‖ + ‖c y (s' * g) - c y x‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
      _ ≤ ε := by linarith
  · exact (norm_sub_le _ _).trans (by linarith [hsmall φ hφ, hsmall (c y) hψ])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMemSUAdelic
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem idem_mul (e : R) (he : e * e = e) (A B : Matrix n n R) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 + e • (A * B - 1) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add]
  abel

theorem idem_cT (c : R →+* R) (e : R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, hc, eq_comm]

theorem idem_unitary (c : R →+* R) (e : R) (he : e * e = e) (hc : c e = e) (J A : Matrix n n R)
    (hA : Formalism.UG.cT c A * J * A = J) :
    Formalism.UG.cT c (1 + e • (A - 1)) * J * (1 + e • (A - 1)) = J := by
  rw [idem_cT c e hc]
  have : (1 + e • (Formalism.UG.cT c A - 1)) * J * (1 + e • (A - 1)) =
      J + e • (Formalism.UG.cT c A * J * A - J) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add, Matrix.mul_assoc]
    abel
  rw [this, hA, sub_self, smul_zero, add_zero]

theorem idem_det (e : R) (he : e * e = e) (A : Matrix n n R) (hA : A.det = 1) :
    (1 + e • (A - 1)).det = 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Matrix.det_isEmpty
  have hpow : ∀ f : R, f * f = f → ∀ k : ℕ, f ^ (k + 1) = f := by
    intro f hf k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hf]
  have hk : Fintype.card n = (Fintype.card n - 1) + 1 := by
    have := Fintype.card_pos (α := n); omega
  have h1 : e • (1 + e • (A - 1)) = e • A := by
    rw [smul_add, smul_smul, he, smul_sub]; abel
  have h2 : (1 - e) • (1 + e • (A - 1)) = (1 - e) • (1 : Matrix n n R) := by
    rw [smul_add, smul_smul, show (1 - e) * e = 0 by rw [sub_mul, one_mul, he, sub_self], zero_smul, add_zero]
  have he' : (1 - e) * (1 - e) = 1 - e := by ring_nf; rw [sq, he]; ring
  have d1 := congrArg Matrix.det h1
  have d2 := congrArg Matrix.det h2
  rw [Matrix.det_smul, Matrix.det_smul, hk, hpow e he, hA] at d1
  rw [Matrix.det_smul, Matrix.det_smul, hk, hpow _ he', Matrix.det_one] at d2
  linear_combination d1 + d2

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qr (x : Fin M → E) (u : E) : Matrix (Fin M) (Fin M) E :=
  1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (Matrix.vecMul (fun i => σ (x i)) J)

theorem sigR_inclR (e : E) : sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

def rmat (g : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  RingHom.mapMatrix (inclR (AF F)) (g : Matrix (Fin M) (Fin M) E)

theorem cT_rmat (g : GL (Fin M) E) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) =
      RingHom.mapMatrix (inclR (AF F)) (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)) := by
  ext i j
  simp [rmat, Formalism.UG.cT, sigR_inclR]

theorem rmat_unitary {g : GL (Fin M) E} (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) * JR (AF F) J * rmat (F := F) g = JR (AF F) J := by
  have h : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  rw [cT_rmat, show JR (AF F) J = RingHom.mapMatrix (inclR (AF F)) J from rfl, rmat, ← map_mul, ← map_mul, h]

def tm (η : AF F) (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  1 + algebraMap (AF F) (AF F ⊗[F] E) η • (A - 1)

theorem tm_mul (η : AF F) (hη : η * η = η) (A B : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    tm η A * tm η B = tm η (A * B) :=
  idem_mul _ (by rw [← map_mul, hη]) A B

def trunc (η : AF F) (hη : η * η = η) : Formalism.UG.UJ (σ : E →+* E) J →* HA (AF F) σ J where
  toFun g := (⟨⟨tm η (rmat g.1), tm η (rmat g.1⁻¹),
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero],
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero]⟩,
    idem_unitary _ _ (by rw [← map_mul, hη]) (StrongApprox.sigR_algebraMap σ η) _ _ (rmat_unitary σ J g.2)⟩ : HR (AF F) σ J)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (1 : GL (Fin M) E)) = 1
    rw [rmat, Units.val_one, map_one, tm, sub_self, smul_zero, add_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (g.1 * h.1)) = tm η (rmat g.1) * tm η (rmat h.1)
    rw [tm_mul η hη, rmat, rmat, rmat, ← map_mul, Units.val_mul]

theorem mv_trunc (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) :
    ((HA.mat (AF F) σ J (trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g.1 - 1) := rfl

theorem trunc_mem_SUAdelic (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J)
    (hg : (g.1 : Matrix (Fin M) (Fin M) E).det = 1) : trunc σ J η hη g ∈ SUAdelic σ J := by
  rw [StrongApprox.mem_SUAdelic, mv_trunc]
  refine idem_det _ (by rw [← map_mul, hη]) _ ?_
  rw [rmat, ← RingHom.map_det, hg, map_one]

theorem idem_mul_of_sub {S₁ S₁' : Finset (InfinitePlace F)} {S₂ S₂' : Finset (HeightOneSpectrum (𝓞 F))}
    {ε ε' : AF F} (h : IsPlacesIdem S₁ S₂ ε) (h' : IsPlacesIdem S₁' S₂' ε') (hS₁ : S₁' ⊆ S₁) (hS₂ : S₂' ⊆ S₂) :
    ε * ε' = ε' := by
  obtain ⟨a1, -, b1, -⟩ := h
  obtain ⟨-, a0', -, b0'⟩ := h'
  apply Prod.ext
  · funext w
    change fstA F ε w * fstA F ε' w = fstA F ε' w
    by_cases hw : w ∈ S₁'
    · rw [a1 w (hS₁ hw), one_mul]
    · rw [a0' w hw, mul_zero]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε') = evalV F v (sndA F ε')
    by_cases hv : v ∈ S₂'
    · rw [b1 v (hS₂ hv), one_mul]
    · rw [b0' v hv, mul_zero]

theorem idem_sq {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε :=
  idem_mul_of_sub h h subset_rfl subset_rfl

theorem SUSupp_mono {ε ε' : AF F} (hε : ε * ε' = ε') {g : HA (AF F) σ J} (hg : g ∈ SUSupp σ J ε') :
    g ∈ SUSupp σ J ε := by
  refine ⟨hg.1, fun i j => ?_⟩
  rw [← hg.2 i j, ← mul_assoc, ← map_mul, hε]

end GlobalTheory.SUAssemble
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMemIdentityComponents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem unit_mem_identityComponents (S : Scheme.{0}) (G : Over S) [GrpObj G] (s : S) :
    (η[G]).left s ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  have hs : G.hom ((η[G]).left s) = s := by
    have h := Over.w (η[G])
    have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [h2] at h
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  show (η[G]).left s ∈ connectedComponentIn (G.hom ⁻¹' {G.hom ((η[G]).left s)}) ((η[G]).left (G.hom ((η[G]).left s)))
  rw [hs]
  exact mem_connectedComponentIn hs

theorem identityComponentOpen : GlobalTheory.Published.IdentityComponentOpen := by
  intro S G _ hG
  obtain ⟨G₀, i, j, h1, h2, h3⟩ := _root_.GlobalTheory.OpenSubgroup.exists_open_subgroup S G
    {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}
    (_root_.GlobalTheory.IdCompOpen.isOpen_identityComponent S G hG) (unit_mem_identityComponents S G) (_root_.GlobalTheory.IdCompMul.mul_mem S G hG) (GlobalTheory.T.inv_mem_identity_component_fibre S G)
  refine ⟨G₀, i, j, h1, h2, fun x => ?_⟩
  rw [h3]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationTwelfthPowerOfCube
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

private lemma twelfth_power_clear_denom_three_mod_eight (p : ℕ) (D A Q s : ℂ) (n : ℕ) (hp0 : (p:ℂ) ≠ 0) (hD0 : D ≠ 0)
    (hQ0 : Q ≠ 0) (hs2 : s^2 = 1) (hε : Q^4 * (p:ℂ)^3 = s * D^(4*n+1)) :
    (A*D^n/(Q*p))^12 * (p:ℂ)^3 * D^3 * s = A^12 := by
  have h3 : Q^12 * (p:ℂ)^9 = s * D^(12*n+3) := by
    calc Q^12 * (p:ℂ)^9 = (Q^4 * (p:ℂ)^3)^3 := by ring
      _ = s^2 * s * D^(12*n+3) := by rw [hε]; ring
      _ = _ := by rw [hs2]; ring
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_iff (by positivity)]
  linear_combination (-(A^12 * (p:ℂ)^3)) * h3

private lemma twelfth_power_clear_denom_seven_mod_eight (p : ℕ) (D A Q s : ℂ) (n : ℕ) (hD0 : D ≠ 0)
    (hs2 : s^2 = 1) (hε : Q^4 * (p:ℂ)^3 = s * D^(4*n+3)) :
    (A*Q/D^(n+1))^12 * (p:ℂ)^9 * D^3 * s = A^12 := by
  have h3 : Q^12 * (p:ℂ)^9 = s * D^(12*n+9) := by
    calc Q^12 * (p:ℂ)^9 = (Q^4 * (p:ℂ)^3)^3 := by ring
      _ = s^2 * s * D^(12*n+9) := by rw [hε]; ring
      _ = _ := by rw [hs2]; ring
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_iff (by positivity)]
  linear_combination (A^12 * D^3 * s) * h3 + (A^12 * D^(12*n+12)) * hs2

private lemma twelfth_cancel (V : ValuationSubring ℂ) (D A u P s : ℂ) (e : ℕ) (hD0 : D ≠ 0)
    (hs2 : s^2 = 1) (hv : V.valuation A ^ 3 = V.valuation D)
    (h : u^12 * P^e * D^3 * s = A^12) :
    V.valuation u ^ 12 * V.valuation P ^ e = V.valuation D := by
  have hs : V.valuation s = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs2.trans (one_pow 2).symm) with h1 | h1 <;>
      simp [h1]
  have h' := congrArg V.valuation h
  simp only [map_mul, map_pow, hs, mul_one] at h'
  have hD' : V.valuation D ^ 3 ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 hD0)
  apply mul_right_cancel₀ hD'
  rw [h', show 12 = 3 * 4 from rfl, pow_mul, hv, ← pow_succ']

theorem valuation_twelfth_power_of_cube :
    ∀ (p : ℕ) (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (D A Q : ℂ), p % 4 = 3 →
      D ∈ F → A ∈ F → Q ∈ F → D ≠ 0 → A ≠ 0 → V.valuation A ^ 3 = V.valuation D →
      Q ^ 8 * (p : ℂ) ^ 6 = D ^ (p - 1) →
      ∃ u ∈ F, u ≠ 0 ∧ V.valuation u ^ 12 * V.valuation (p : ℂ) ^ (if p % 8 = 3 then 3 else 9)
        = V.valuation D := by
  intro p V F D A Q hp hD hA hQ hD0 hA0 hv hrel
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [show p - 1 = 2 * (2 * k + 1) by omega, pow_mul'] at hrel
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hrel
    exact pow_ne_zero _ (pow_ne_zero _ hD0) hrel.symm
  have hsq : (Q^4 * (p:ℂ)^3)^2 = (D^(2*k+1))^2 := by rw [← hrel]; ring
  obtain ⟨s, hs2, hε⟩ : ∃ s : ℂ, s^2 = 1 ∧ Q^4 * (p:ℂ)^3 = s * D^(2*k+1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨1, by norm_num, by rw [h, one_mul]⟩
    · exact ⟨-1, by norm_num, by rw [h, neg_one_mul]⟩
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring] at hε
    refine ⟨A * D^n / (Q * p), div_mem (mul_mem hA (pow_mem hD n)) (mul_mem hQ (natCast_mem F p)),
      div_ne_zero (mul_ne_zero hA0 (pow_ne_zero _ hD0)) (mul_ne_zero hQ0 hp0), ?_⟩
    rw [if_pos (by omega)]
    exact twelfth_cancel V D A _ _ s 3 hD0 hs2 hv (twelfth_power_clear_denom_three_mod_eight p D A Q s n hp0 hD0 hQ0 hs2 hε)
  · rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by ring] at hε
    refine ⟨A * Q / D^(n+1), div_mem (mul_mem hA hQ) (pow_mem hD _),
      div_ne_zero (mul_ne_zero hA0 hQ0) (pow_ne_zero _ hD0), ?_⟩
    rw [if_neg (by omega)]
    exact twelfth_cancel V D A _ _ s 9 hD0 hs2 hv (twelfth_power_clear_denom_seven_mod_eight p D A Q s n hD0 hs2 hε)

end GlobalTheory
end

