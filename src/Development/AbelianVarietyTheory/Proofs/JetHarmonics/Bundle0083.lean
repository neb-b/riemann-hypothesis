module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
public import Formalism.HermitianCurvature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeries
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowestVector


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.LowestVector.exists_lowest_vector : _root_.PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : _root_.BranchingSupport.Rep k r), R.IsDS ε mu → ∀ (Q : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), _root_.PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ _root_.Formalism.REAL.KHighest ε E (_root_.Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (_root_.Formalism.REAL.kSpan ε E w) := by
  intro hKS k r ε mu R hDS Q E hQ hE
  have hFV := (_root_.GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hDS Q hQ
  unfold _root_.PI.UpqRep.IsDS at hFV
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hFV
  unfold _root_.PI.UpqRep.IsKTypeOf at hS
  obtain ⟨hSfd, hSK, -, ⟨v, hvS, hv0, hvw⟩, hhigh⟩ := hS
  have hlow : _root_.PI.UpqRep.lowK ε mu = _root_.Formalism.QuantumDeterminants.lowK ε mu := rfl
  have hstab := _root_.GlobalTheory.CompactStable.kStable_smooth_and_stable hKS k r ε mu R hDS Q hQ S hSfd hSK
  unfold _root_.BranchingSupport.Rep.IsE at hE
  set w0 : R.H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw0def
  have hw0S : w0 ∈ S := S.smul_mem _ hvS
  have hw0wt : _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) (fun g ↦ R.σ (Q⁻¹ * g * Q)) (_root_.PI.UpqRep.lowK ε mu) w0 := by
    unfold _root_.PI.UpqRep.IsWtOn at hvw ⊢
    intro θ hθ
    rw [hw0def, ContinuousLinearMap.map_smul, hvw θ hθ, smul_comm]
  have hnorm : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  let w : R.smSub := ⟨w0, (hstab.1 w0 hw0S).2⟩
  have htor := _root_.GlobalTheory.TorusWeight.torus_weight_action hKS k r ε mu R hDS Q E hQ hE (_root_.PI.UpqRep.lowK ε mu) w hw0wt
  let T : Submodule ℂ R.smSub := S.comap R.smSub.subtype
  have hT : _root_.Formalism.REAL.KStable ε E T := by
    unfold _root_.Formalism.REAL.KStable
    intro a b hab x hx
    show ((E a b x : R.smSub) : R.H) ∈ S
    rw [hE]
    exact hstab.2 a b hab x hx
  have hTfd : FiniteDimensional ℂ T := by
    let f : T →ₗ[ℂ] S :=
      LinearMap.codRestrict S (R.smSub.subtype.comp T.subtype) (fun x => x.2)
    refine Module.Finite.of_injective f ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    exact hval
  have hle : _root_.Formalism.REAL.kSpan ε E w ≤ T := by
    unfold _root_.Formalism.REAL.kSpan
    exact sInf_le ⟨hw0S, hT⟩
  refine ⟨w, hnorm, (hstab.1 w0 hw0S).1, ?_, Submodule.finiteDimensional_of_le hle⟩
  unfold _root_.Formalism.REAL.KHighest
  refine ⟨htor.1, ?_⟩
  intro a b hab hεab
  by_contra hne
  have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
    rw [hE]
    exact hstab.2 a b hεab w0 hw0S
  have hne' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => hne (Submodule.coe_eq_zero.mp h)
  exact _root_.GlobalTheory.DominantRootSums.not_cDom_add_root _ ε (_root_.PI.UpqRep.lowK ε mu) a b hab
    (hhigh _ _ hmem hne' (htor.2 a b))

end GlobalTheory.LowestVector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFinOrd

theorem exists_pow_mul_eq_one {F A : Type} [Field F] [Ring A] [Algebra F A] (U W : A) (e : F)
    (h : U * W = e • (W * U)) {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M') (hU : U ^ M = 1) (hW : W ^ M' = 1) :
    ∃ n, 1 ≤ n ∧ (U * W) ^ n = 1 := by
  have h₁ : ∀ i : ℕ, U ^ i * W = e ^ i • (W * U ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', _root_.mul_assoc, ih, mul_smul_comm, ← _root_.mul_assoc, h, smul_mul_assoc, smul_smul,
        _root_.mul_assoc, pow_succ e]
  have h₂ : ∀ n : ℕ, ∃ t : ℕ, (U * W) ^ n = e ^ t • (W ^ n * U ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (n + 1), ?_⟩
      rw [pow_succ, ht, smul_mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (U ^ n), ← pow_succ, h₁,
        mul_smul_comm, smul_smul, ← pow_add, ← _root_.mul_assoc, ← pow_succ]
  have h₃ : e ^ M • (1 : A) = 1 := by
    have a := h₁ M
    rw [hU, _root_.one_mul, _root_.mul_one] at a
    obtain ⟨m, rfl⟩ : ∃ m, M' = m + 1 := ⟨M' - 1, by omega⟩
    have b : W ^ m * W = W ^ m * (e ^ M • W) := congrArg _ a
    rw [mul_smul_comm, ← pow_succ, hW] at b
    exact b.symm
  obtain ⟨t, ht⟩ := h₂ (M * M')
  refine ⟨M * M' * M, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
  rw [pow_mul U, hU, one_pow, mul_comm M M', pow_mul W, hW, one_pow, _root_.mul_one] at ht
  rw [mul_comm M M', pow_mul, ht, smul_pow, one_pow, ← pow_mul, mul_comm t M, pow_mul]
  have := congrArg (· ^ t) h₃
  simpa only [smul_pow, one_pow] using this

theorem isAdd_symm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : ∀ x a b, th D (T := TF (R := R) F) y J x a b =
      th D (T := TF (R := R) F) y J x b a := by
    intro x a b
    have := (val_corr hJ D.cub.cubeSymmetric_swap_last (lift x (lift a b)).left).trans
      (val_cub D.cub (lift x (lift a b)) hJ _ _ _)
    refine Eq.trans this ?_
    congr 1 <;> simp [x3]
  rw [C, h.2 χ y J hJ, mul_comm]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_scalar (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D.toPre F k)
    (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)))
    (hw : w.IsGen) (hw' : w'.IsGen) (Φ Φ' : Fam D.toPre F k →ₗ[F] Fam D.toPre F k)
    (hΦ : ∀ s, PhiRel D.toPre F k p w s (Φ s)) (hΦ' : ∀ s, PhiRel D.toPre F k p w' s (Φ' s)) :
    ∃ c : F, Φ = c • Φ' := by
  obtain ⟨c, -, hc⟩ := TWM.exists_ratio (F := F) D.toPre.P.isLB w hw w' hw' (fun _ _ _ => rfl)
  refine ⟨c, LinearMap.ext fun s => ?_⟩
  refine phi_unique p w ((phiRel_iff hG p w hw _ _).1 (hΦ s)) ?_
  intro a β hβ T ρ z J hJ
  have h1 := (phiRel_iff hG p w' hw' s (Φ' s)).1 (hΦ' s) a β hβ T ρ z J hJ
  have h2 := hc _ (ρ ≫ fst (TF (R := V) F) D.toPre.P.A).left z J hJ
  rw [LinearMap.smul_apply, sval_smul c (Φ' s) β ρ.left z hJ, h1, val_mul hJ, val_mul hJ]
  simp only [Units.val_mul]
  have alg : ∀ {S : Type} [CommRing S] (g a u x y y' : S), y = g * y' →
      g * (a * (u * (x * y'))) = a * (u * (x * y)) := fun g a u x y y' h => by rw [h]; ring
  exact alg _ _ _ _ _ _ h2

theorem finOrd_iff {k : ℕ} (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ : F)
    (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) :
    FinOrd D F k p w ζ ↔ ∃ M : ℕ, 1 ≤ M ∧ ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) = 1 := by
  constructor
  · rintro ⟨M, hM, H⟩
    refine ⟨M, hM, LinearMap.ext fun s => ?_⟩
    have := H (fun i => ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)
      (fun i => Φ (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)) (fun i => ⟨(hΦ _ _).2 rfl, by
        rw [DVR.isSmul_iff, Fin.val_succ, pow_succ', Module.End.mul_apply, LinearMap.smul_apply]⟩)
    exact fam_ext this
  · rintro ⟨M, hM, hpow⟩
    refine ⟨M, hM, fun ss ts H α j => ?_⟩
    have hstep : ∀ i : Fin M, ss i.succ = (ζ • Φ) (ss i.castSucc) := by
      intro i
      obtain ⟨h1, h2⟩ := H i
      rw [hΦ] at h1
      rw [DVR.isSmul_iff] at h2
      rw [h2, h1, LinearMap.smul_apply]
    have hall : ∀ i : ℕ, ∀ hi : i < M + 1,
        ss ⟨i, hi⟩ = ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ i) (ss 0) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
        exact hstep ⟨i, by omega⟩
    have hlast : ss (Fin.last M) = ss 0 := by
      rw [show Fin.last M = ⟨M, Nat.lt_succ_self M⟩ from rfl, hall M (Nat.lt_succ_self M), hpow]
      rfl
    rw [hlast]

theorem exists_pow_scalar (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (Φ : Module.End F (Fam D.toPre F k)) (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) :
    ∃ c : F, Φ ^ k = c • 1 := by
  obtain ⟨c, -, hc⟩ := phiPow_of_globalFns hG V _ D F k hk p w hw
  refine ⟨c, LinearMap.ext fun s => ?_⟩
  have := hc (fun i => (Φ ^ (i : ℕ)) s) (fun i => (hΦ _ _).2 (by
    rw [Fin.val_succ, pow_succ', Module.End.mul_apply]; rfl))
  rw [DVR.isSmul_iff] at this
  exact this

end GlobalTheory.ThetaFinOrd

namespace GlobalTheory


open ThetaFinOrd in
theorem finOrd_criteria : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ (p : QkPt D.toPre F k) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))), w.IsGen → ∀ (ζ : F) (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) → ∀ (s : Fam D.toPre F k) (M : ℕ), s ≠ 0 → 1 ≤ M → ((ζ • Φ) ^ M) s = s → FinOrd D F k p w ζ) ∧ ∀ (p p₁ p₂ : QkPt D.toPre F k), p₂.y = p.y + p₁.y → p.g.IsAdd p₁.g p₂.g → ∀ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε k))) (w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε k))), w.IsGen → w₁.IsGen → w₂.IsGen → (∀ s t t' : Fam D.toPre F k, PhiRel D.toPre F k p₁ w₁ s t → PhiRel D.toPre F k p w t t' → PhiRel D.toPre F k p₂ w₂ s t') → ∀ ζ ζ₁ : F, FinOrd D F k p w ζ → FinOrd D F k p₁ w₁ ζ₁ → FinOrd D F k p₂ w₂ (ζ * ζ₁) := by
  intro hL V _ _ _ D F _ _ k hk
  have hG := hL.globalFns
  refine ⟨fun p w hw ζ Φ hΦ s M hs hM hfix => ?_, fun p p₁ p₂ hy hg w w₁ w₂ hw hw₁ hw₂ hc ζ ζ₁ h h₁ => ?_⟩
  · obtain ⟨c, hc⟩ := exists_pow_scalar hG hk p w hw Φ hΦ
    have e : ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ k = ((ζ ^ k * c) ^ M) • 1 := by
      rw [← pow_mul, mul_comm M k, pow_mul, smul_pow, hc, smul_smul, smul_pow, one_pow]
    have f : ∀ n : ℕ, (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ n) s = s := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
    have g := f k
    rw [e, LinearMap.smul_apply, Module.End.one_apply] at g
    have g' : (ζ ^ k * c) ^ M = 1 := by
      have : ((ζ ^ k * c) ^ M - 1) • s = 0 := by rw [sub_smul, g, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)
    refine (finOrd_iff p w ζ Φ hΦ).2 ⟨M * k, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
    rw [pow_mul, e, g', one_smul]
  · obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ D F k hk p w hw
    obtain ⟨Φ₁, hΦ₁⟩ := phiFun_of_globalFns hG V _ D F k hk p₁ w₁ hw₁
    obtain ⟨Φ₂, hΦ₂⟩ := phiFun_of_globalFns hG V _ D F k hk p₂ w₂ hw₂
    obtain ⟨w', hw', hc'⟩ := ThetaMul.phi_mul_core hG p₁ p p₂ (hy.trans (add_comm _ _)) (isAdd_symm hg)
      w₁ w hw₁ hw
    have e₂ : Φ₂ = (Φ * Φ₁ : Module.End F (Fam D.toPre F k)) := LinearMap.ext fun s =>
      ((hΦ₂ _ _).1 (hc s _ _ ((hΦ₁ _ _).2 rfl) ((hΦ _ _).2 rfl))).symm
    obtain ⟨e, he⟩ := exists_scalar hG p₂ w₂ w' hw₂ hw' Φ₂ (Φ₁ * Φ : Module.End F (Fam D.toPre F k))
      (fun s => (hΦ₂ _ _).2 rfl) (fun s => hc' s _ _ ((hΦ _ _).2 rfl) ((hΦ₁ _ _).2 rfl))
    obtain ⟨M, hM, hU⟩ := (finOrd_iff p w ζ Φ hΦ).1 h
    obtain ⟨M', hM', hW⟩ := (finOrd_iff p₁ w₁ ζ₁ Φ₁ hΦ₁).1 h₁
    have m : (ζ • Φ : Module.End F (Fam D.toPre F k)) * (ζ₁ • Φ₁ : Module.End F (Fam D.toPre F k)) =
        (ζ * ζ₁) • Φ₂ := by
      rw [e₂, smul_mul_smul_comm]
    obtain ⟨n, hn, hp⟩ := exists_pow_mul_eq_one (F := F) (A := Module.End F (Fam D.toPre F k)) (ζ • Φ) (ζ₁ • Φ₁) e
      (by rw [m, he, smul_mul_smul_comm, smul_comm, mul_comm ζ₁ ζ]) hM hM' hU hW
    rw [m] at hp
    exact (finOrd_iff p₂ w₂ _ Φ₂ hΦ₂).2 ⟨n, hn, hp⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTensorStandardRep
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

noncomputable section

namespace GlobalTheory.TensorStd

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {k : ℕ}

def tenOp (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V) :
    PiLp 2 (fun _ : Fin k => V) →L[ℂ] PiLp 2 (fun _ : Fin k => V) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun c => ∑ d, C c d • (A ∘L PiLp.proj 2 (fun _ : Fin k => V) d)

theorem tenOp_apply (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    tenOp C A y c = ∑ d, C c d • A (y d) := by
  simp [tenOp]

private lemma inner_map_of_norm_eq (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) (u w : V) :
    inner ℂ (A u) (A w) = inner ℂ u w :=
  (⟨A.toLinearMap, hA⟩ : V →ₗᵢ[ℂ] V).inner_map_map u w

theorem tenOp_norm (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V)
    (hC : ∀ d e, ∑ c, C c e * star (C c d) = if e = d then 1 else 0) (hA : ∀ v, ‖A v‖ = ‖v‖)
    (y : PiLp 2 (fun _ : Fin k => V)) : ‖tenOp C A y‖ = ‖y‖ := by
  have key : inner ℂ (tenOp C A y) (tenOp C A y) = inner ℂ y y := by
    simp only [PiLp.inner_apply, tenOp_apply, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, inner_map_of_norm_eq A hA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ e, ∑ c, C c d * ((starRingEnd ℂ) (C c e) * inner ℂ (y e) (y d)) =
        (if d = e then 1 else 0) * inner ℂ (y e) (y d) := by
      intro e
      rw [← hC e d, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Complex.star_def]
      ring
    simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]

end GlobalTheory.TensorStd

namespace GlobalTheory

open TensorStd

private lemma herm_sum_smul_left' {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m → ℂ)
    (w : Fin m → Fin n → ℂ) (u : Fin n → ℂ) :
    herm H (∑ c, a c • w c) u = ∑ c, a c * herm H (w c) u := by
  simp [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]

private lemma herm_sum_smul_right' {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m → ℂ)
    (w : Fin m → Fin n → ℂ) (v : Fin n → ℂ) :
    herm H v (∑ c, a c • w c) = ∑ c, star (a c) * herm H v (w c) := by
  simp [herm, star_sum, sum_dotProduct, star_smul, smul_dotProduct]

theorem exists_tensor_standard_rep :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → ∃ πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V))), IsRepW k r z πt ∧ (∀ h ∈ UWset k r z, ∀ v, ‖πt h v‖ = ‖v‖) ∧ (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) := by
  intro V _ _ _ k r z π B hz hT hπ hiso hB
  obtain ⟨hcomp, hgrp⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB

  have hexp : ∀ h ∈ UWset k r z, ∀ d,
      h *ᵥ B d = ∑ e, herm (Hpk k r) (h *ᵥ B d) (B e) • B e := by
    intro h hh d
    obtain ⟨h1, h2⟩ := (hgrp h hh).1 (B d) (hB.1 d) (hB.2.2 d z (List.mem_singleton_self z))
    exact hcomp _ h1 h2
  refine ⟨fun h => tenOp (fun c d => herm (Hpk k r) (h *ᵥ B d) (B c)) (π h), ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => PiLp.ext fun c => ?_
    rw [tenOp_apply, hπ.1.1]
    simp [hB.2.1]
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun y => PiLp.ext fun c => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.comp_apply, tenOp_apply, hπ.1.2 a ha b hb, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    conv_lhs => rw [← Matrix.mulVec_mulVec, hexp b hb d, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rw [herm_sum_smul_left']
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · rw [continuousOn_clm_apply]
    intro y
    have hrepr : ∀ h, tenOp (fun c d => herm (Hpk k r) (h *ᵥ B d) (B c)) (π h) y =
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => V)).symm
          (fun c => ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) := by
      intro h
      exact PiLp.ext fun c => by rw [tenOp_apply]; rfl
    simp only [hrepr]
    refine (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous.comp_continuousOn ?_
    refine continuousOn_pi.2 fun c => continuousOn_finsetSum _ fun d _ => ?_
    refine ContinuousOn.smul ?_ (hπ.2.clm_apply continuousOn_const)
    exact Continuous.continuousOn (by unfold herm; fun_prop)
  · intro h hh y
    refine tenOp_norm _ _ (fun d e => ?_) (hiso h hh) y
    have hpres := (hgrp h hh).2.1 (B e) (B d)
    rw [hB.2.1 e d] at hpres
    rw [← hpres]
    conv_rhs => rw [hexp h hh d, herm_sum_smul_right']
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · intro h hh y c
    exact tenOp_apply _ _ _ _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyFunctionalCoefficient
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_coef_family : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ), IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R 0) (l 0) (l' 0) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J 0 = (fun g => (t : ℂ) • f g) ∧ (NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg f s₀ hfam hL hR hf hs₀
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have h0 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  have hDS : ∀ ν, n1 ν ≤ q0 → (R ν).IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ)) :=
    fun ν hν => hfam ν hν
  have hdg0 : 0 < dg 0 := (hL 0 h0).2.1
  have hsn : 0 < ‖s₀‖ := norm_pos_iff.mpr hs₀
  have hnz : NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0) := by
    obtain ⟨m, x, y, X, hxy, -, hs⟩ := hf
    have hsm := (GlobalTheory.rep_basic_of_isDS hK _ _ _ _ (R 0) (hDS 0 h0)).2.2.2.2.1
    rw [hs] at hs₀
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs₀
    refine ⟨⟨x i, hsm _ (hxy i).1, fun h => hi ?_⟩, ⟨y i, hsm _ (hxy i).2, fun h => hi ?_⟩⟩
    · rw [h, inner_zero_left]
    · rw [h, map_zero, inner_zero_right]
  have hex : ∀ ν, ∃ (s : ℂ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (ν = 0 → F = fun g => ((dg 0 / ‖s₀‖ : ℝ) : ℂ) • f g) ∧
      (n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) F s ∧ ‖s‖ = dg ν) ∧
      (¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → F = 0) := by
    intro ν
    by_cases hν : ν = 0
    · subst hν
      refine ⟨((dg 0 / ‖s₀‖ : ℝ) : ℂ) * s₀, _, fun _ => rfl, fun _ _ _ => ⟨?_, ?_⟩, fun hn => ?_⟩
      · exact (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R 0) Wp Wq (l 0) (l' 0) (hDS 0 h0)).2.1 f s₀ _ hf
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hdg0 hsn).le]
        field_simp
      · exact absurd ⟨h0, hnz⟩ hn
    · by_cases hc : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
      · obtain ⟨h1, h2, h3⟩ := hc
        have e1 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wp _ _ (l ν) (hDS ν h1) (hL ν h1).1.1 h2
        have e2 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wq _ _ (l' ν) (hDS ν h1) (hR ν h1).1.1 h3
        obtain ⟨F, hF⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν) Wp Wq (l ν) (l' ν)
          (hDS ν h1)).2.2 e1 e2 (dg ν : ℂ)
        refine ⟨_, F, fun h => absurd h hν, fun _ _ _ => ⟨hF, ?_⟩, fun hn => absurd ⟨h1, h2, h3⟩ hn⟩
        rw [Complex.norm_real, Real.norm_of_nonneg (hL ν h1).2.1.le]
      · exact ⟨0, 0, fun h => absurd h hν, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc, fun _ => rfl⟩
  choose s J h1 h2 h3 using hex
  exact ⟨s, J, dg 0 / ‖s₀‖, div_pos hdg0 hsn, h1 0 rfl, hnz, h2, h3⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HypAndAdj
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.TypeGlModule

theorem hyp_and_adj :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ)
      (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ)
      (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)),
      inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L →
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) →
      IsFrameOf (n + 1) r [z] B →
      Hyp (EB π B) β L ∧ ∀ a b x y, inner ℂ (EB π B a b x) y = inner ℂ x (EB π B b a y) := by
  intro V _ _ _ n r z π u β L B hz hT hty hL hu hB
  obtain ⟨hnt, hrep, hcont, hunit, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨hgl, hq⟩ := Formalism.FourierDecayAlt.P.frame_general_linear V (n + 1) r (n + 1) z π B hR hB
  refine ⟨?_, fun a b x y => Formalism.FourierDecayAlt.P5.Kfp.EB_adj hrep hcont hunit hB a b x y⟩
  refine ⟨hgl, ⟨hnt, fun S hS =>
    hirr S (Formalism.FourierDecayAlt.P.lie_stabilizer V (n + 1) r z π B hz hT hR hB S hS)⟩, hL, ?_⟩
  intro w v
  rw [← hq w v, hcap B hB w v, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
  congr 1
  unfold cpol shf
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← hu j]
  ring

end GlobalTheory.TypeGlModule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransferStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_bessel_transfer : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  first | exact @GlobalTheory.herm_smul_eq_sum_of_tensRaw | exact GlobalTheory.herm_smul_eq_sum_of_tensRaw | (intros; apply GlobalTheory.herm_smul_eq_sum_of_tensRaw <;> assumption)
end

