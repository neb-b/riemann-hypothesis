module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicWeilVacuumFixedAndTranslatesSpan
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Vacuum

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := _root_.GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  exact h2 ▸ (h1 1).2

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, map_nsmul]
  exact smul_comm _ _ _

theorem map_nsmul_inc (D : D7) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (m • z).map (inc D) = m • z.map (inc D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]

theorem nsmul_inv_smul {X : Type*} [AddCommGroup X] [Module ℚ X] {m : ℕ} (hm : 0 < m) (a : X) :
    m • ((m : ℚ)⁻¹ • a) = a := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hm.ne'), one_smul]

theorem level_fixed {D : D7} (hg : admG1 D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {w : 𝓞 D.host.E} {γ : XA D N N' → XA D N N' → ℂ}
    {WA : XA D N N' → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N'}
    (hM : GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA) (v : TTs D (tor0 D cc δ) N N') (m : ℕ)
    (hv : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (m • x) v = v) :
    ∀ b ∈ latA D cc N N', WA (m • b) v = v := by
  intro b hb
  obtain ⟨-, -, -, hW, hC⟩ := hM
  obtain ⟨h1, -, h3, -⟩ := _root_.GlobalTheory.CompletedLattice.completed_lattice D hg cc δ hc N N'
  obtain ⟨m', hm', h⟩ := hC (m • b) v
  obtain ⟨z, a, ha, hz⟩ := h3 b m' hm'
  have hz' : pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N' := by
    rw [← h1, hz]
    exact add_mem hb (nsmul_mem ha _)
  have e : (m • z).map (inc D) = m • b + m' • (m • a) := by
    rw [map_nsmul_inc, hz, smul_add, smul_comm m m' a]
  rw [← h _ (nsmul_mem ha m), ← e]
  apply Subtype.ext
  rw [hW, pt_nsmul]
  exact hv _ hz'

theorem vacuum_fixed_span : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ h : e0 ∈ TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') ⟨e0, h⟩ ∧ Submodule.span ℂ (Set.range fun ζ => WA ζ ⟨e0, h⟩) = ⊤ := by
  intro D hg cc δ hc N N' w γ WA hM e0 he0 hne
  obtain ⟨hL, hWd, -⟩ := _root_.GlobalTheory.ThetaLine.theta_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, sd_std D _, sd_std D _, rfl⟩)
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.CompletedLattice.completed_lattice D hg cc δ hc N N'
  have h0 : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) ((1 : ℕ) • x) e0 = e0 := fun x hx => by
    rw [one_smul, hWd x hx]
    funext z
    exact he0.2 x hx z
  have hT : e0 ∈ TTs D (tor0 D cc δ) N N' := ⟨he0.1, 1, one_pos, h0⟩
  refine ⟨hT, fun a ha => ?_, ?_⟩
  · have := level_fixed hg hc hM ⟨e0, hT⟩ 1 h0 a ha
    rwa [one_smul] at this
  refine _root_.GlobalTheory.FinWeil.span_translates_vacuum hM.1 _ hM.2.1 _ (fun v hv => ?_) (fun v => ?_)
  · have hv' : (v : VC D N N' → ℂ) ∈ ThSp D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := by
      refine ⟨v.2.1, fun x hx y => ?_⟩
      have e := hWd x hx v
      obtain ⟨z, rfl⟩ := h2 x hx
      rw [← hM.2.2.2.1, hv _ ((h1 z).2 hx)] at e
      exact (congrFun e y).symm
    obtain ⟨c, hc'⟩ := hL _ hv' e0 he0 hne
    exact ⟨c, Subtype.ext hc'⟩
  · obtain ⟨-, m, hm, hv⟩ := v.2
    refine ⟨(latA D cc N N').comap (m • LinearMap.id), _root_.GlobalTheory.FinWeil.idx_latA_ne_zero D hg cc δ hc N N' m hm _ (fun ζ hζ => hζ),
      fun a _ hT' => ?_⟩
    have hb : (m : ℚ)⁻¹ • a ∈ latA D cc N N' := by
      refine (hM.2.1 _).2 fun a' ha' => ?_
      have ht : (m : ℚ)⁻¹ • a' ∈ (latA D cc N N').comap (m • LinearMap.id) := by
        change m • ((m : ℚ)⁻¹ • a') ∈ latA D cc N N'
        rwa [nsmul_inv_smul hm]
      rw [← nsmul_inv_smul hm a', hM.1.nsmul_right, ← hM.1.nsmul_left, nsmul_inv_smul hm]
      exact hT' _ ht
    have := level_fixed hg hc hM v m hv _ hb
    rwa [nsmul_inv_smul hm] at this

end GlobalTheory.FinWeil.Vacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmQuadraticPhaseEquivariantEmbeddings
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.QuadPhase

theorem exists_top_extension (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ) (hS : S.Countable) :
    ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  let M₀ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))
  have hle : M₀ ≤ M := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have hc : Countable M₀ := by
    have h1 := IntermediateField.cardinalMk_adjoin_le ℚ (S ∩ (M : Set ℂ))
    have h2 : (S ∩ (M : Set ℂ)).Countable := hS.mono Set.inter_subset_left
    refine Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))
    · exact Cardinal.mk_le_aleph0
    · exact Cardinal.mk_le_aleph0_iff.2 h2
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M₀)
    (algebraMap M₀ ℂ) ((ρ.comp (IntermediateField.inclusion hle)).toRingHom)
  refine ⟨((σ : ℂ →+* ℂ).toRatAlgHom).comp (IntermediateField.val ⊤), fun x hx hxM => ?_⟩
  have hx0 : x ∈ M₀ := IntermediateField.subset_adjoin ℚ _ ⟨hx, hxM⟩
  have h := hσ ⟨x, hx0⟩
  unfold cj TaylorLogMetric.liftM
  rw [dite_eq_left IntermediateField.mem_top, dite_eq_left hxM]
  exact h

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem cmQuadraticForm_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x = gl3FieldFirst Λ (w0 D * x) x := by
  unfold q1 gl3FieldFirst w0
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.add_im,
    Complex.one_im, Complex.I_re, Complex.I_im]
  ring

theorem cmQuadraticForm_half_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x / 2 = gl3FieldFirst Λ (w0 D * x / 2) x := by
  rw [cmQuadraticForm_eq_alternatingForm]
  unfold gl3FieldFirst
  rw [div_mul_eq_mul_div, Complex.div_ofNat_im]
  ring

theorem cmQuadraticForm_half_add_translation (D : D7) (Λ : AddSubgroup ℂ) (x l : ℂ) (m : ℕ) :
    q1 D Λ (x + 2 * (m : ℂ) * l) / 2 = q1 D Λ x / 2 + gl3FieldFirst Λ (w0 D * ((m : ℂ) * x)) l +
      gl3FieldFirst Λ (w0 D * l) ((m : ℂ) * x) + gl3FieldFirst Λ (w0 D * l) (((2 * m * m : ℕ) : ℂ) * l) := by
  rw [cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm]
  unfold gl3FieldFirst
  rw [← add_div, ← add_div, ← add_div, ← Complex.add_im, ← Complex.add_im, ← Complex.add_im]
  congr 2
  simp only [map_add (f := _), map_mul, map_natCast, map_ofNat]
  push_cast
  ring

theorem phase_top (D : D7) (hS : galStar D) (hW : WeilPairingGaloisAlt D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hc : Crv D cc δ) (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ)
    (x x' : ℂ) (m₀ : ℕ) (hm : 0 < m₀) (hx : (m₀ : ℂ) * x ∈ lamOf D cc δ)
    (hA : Adp1 ⊤ ρ (lamOf D cc δ) (2 * m₀) x x') :
    cj ⊤ ρ (ee (q1 D (lamOf D cc δ) x / 2)) = ee (q1 D (lamConj ⊤ ρ (lamOf D cc δ)) x' / 2) := by
  obtain ⟨hex, huniq, -, hadd, hmul, hord, -⟩ :=
    hS cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  have hWP := hW cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  set Λ := lamOf D cc δ with hΛ
  set Λ' := lamConj ⊤ ρ Λ with hΛ'
  have hm0 : (m₀ : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmulw : ∀ t t', StarPt ⊤ ρ Λ t t' → StarPt ⊤ ρ Λ (w0 D * t) (w0 D * t') := fun t t' h => by
    have := hmul a t t' h
    rwa [ha] at this
  have hw : ∀ l ∈ Λ, w0 D * l ∈ Λ := fun l hl => by
    have h := hmulw l 0 (Or.inl ⟨hl, zero_mem _⟩)
    rcases h with h | h
    · exact h.1
    · exact absurd (by rw [mul_zero]; exact zero_mem _) h.2.1
  have hw' : ∀ l ∈ Λ', w0 D * l ∈ Λ' := fun l hl => by
    have h := hmulw 0 l (Or.inl ⟨zero_mem _, hl⟩)
    rcases h with h | h
    · exact h.2
    · exact absurd (by rw [mul_zero]; exact zero_mem _) h.1
  have hint : ∀ l ∈ Λ', ∀ l' ∈ Λ', ee (gl3FieldFirst Λ' l l') = 1 := fun l hl l' hl' => by
    have h := hWP 0 0 l l' 1 one_pos (by simp) (by simp)
      (Or.inl ⟨by simp, by simpa using hl⟩) (Or.inl ⟨by simp, by simpa using hl'⟩) IntermediateField.mem_top
    rw [← h]
    have h0 : gl3FieldFirst Λ 0 0 = 0 := by simp [gl3FieldFirst]
    rw [h0, ee_zero]
    unfold cj TaylorLogMetric.liftM
    rw [dite_eq_left IntermediateField.mem_top]
    exact map_one ρ
  have hnat : ∀ (A : AddSubgroup ℂ) (n : ℕ), ∀ l ∈ A, (n : ℂ) * l ∈ A := fun A n l hl => by
    rw [← nsmul_eq_mul]
    exact nsmul_mem hl n
  have htn : ((4 * m₀ * m₀ : ℕ) : ℂ) * (x / (4 * (m₀ : ℂ))) = (m₀ : ℂ) * x := by
    push_cast
    field_simp
  obtain ⟨t', ht'⟩ := hex (x / (4 * (m₀ : ℂ))) ⟨4 * m₀ * m₀, by positivity, htn ▸ hx⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  set y : ℂ := 4 * (m₀ : ℂ) * t' with hy
  have hA2 : Adp1 ⊤ ρ Λ (2 * m₀) x y := by
    have h := hadd _ _ _ _ ht' ht'
    unfold Adp1
    convert h using 1
    · push_cast
      field_simp
      ring
    · rw [hy]
      push_cast
      field_simp
      ring
  have hA3 : Adp1 ⊤ ρ Λ (2 * m₀) (w0 D * x / 2) (w0 D * y / 2) := by
    have h := hmulw _ _ ht'
    unfold Adp1
    convert h using 1
    · push_cast
      field_simp
      ring
    · rw [hy]
      push_cast
      field_simp
      ring
  have hl := (huniq _ _ _ hA).1 hA2
  have hμ : (m₀ : ℂ) * y ∈ Λ' := by
    have h := (hord (4 * m₀ * m₀) _ _ ht').1 (htn ▸ hx)
    convert h using 1
    rw [hy]
    push_cast
    ring
  set l : ℂ := x' / ((2 * m₀ : ℕ) : ℂ) - y / ((2 * m₀ : ℕ) : ℂ) with hldef
  have hx' : x' = y + 2 * (m₀ : ℂ) * l := by
    rw [hldef]
    push_cast
    field_simp
    ring
  have hmain := hWP (w0 D * x / 2) x (w0 D * y / 2) y (2 * m₀) (by positivity)
    (by
      convert hw _ hx using 1
      push_cast
      ring)
    (by
      convert hnat Λ 2 _ hx using 1
      push_cast
      ring)
    hA3 hA2 IntermediateField.mem_top
  rw [hx', cmQuadraticForm_half_add_translation, ee_add, ee_add, ee_add, hint _ (hw' _ hμ) _ hl, hint _ (hw' _ hl) _ hμ,
    hint _ (hw' _ hl) _ (hnat Λ' _ _ hl), cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm, hmain]
  simp

theorem galPh1_of (D : D7) (hS : galStar D) (hW : WeilPairingGaloisAlt D) : galPh1 D := by
  intro cc δ hc
  refine ⟨fun x => cmQuadraticForm_eq_alternatingForm D _ x, fun M ρ hK h2 h3 x x' m₀ hm hx hA he => ?_⟩
  set Λ := lamOf D cc δ with hΛ
  have hKc : Countable D.host.K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let S : Set ℂ := Set.range (fun a : D.host.K => D.host.φ₀ (a : D.host.E)) ∪
    {g2 Λ, g3 Λ, wpF Λ (x / ((2 * m₀ : ℕ) : ℂ)), wpD Λ (x / ((2 * m₀ : ℕ) : ℂ)), ee (q1 D Λ x / 2)}
  have hSc : S.Countable := (Set.countable_range _).union (Set.toFinite _).countable
  obtain ⟨σ, hσ⟩ := exists_top_extension M ρ S hSc
  have hK' : FixK D ⊤ σ := fun a =>
    ⟨IntermediateField.mem_top, by rw [hσ _ (Or.inl ⟨a, rfl⟩) (hK a).1, (hK a).2]⟩
  have hl : lamConj ⊤ σ Λ = lamConj M ρ Λ := by
    have e2 := hσ (g2 Λ) (Or.inr (by simp)) h2
    have e3 := hσ (g3 Λ) (Or.inr (by simp)) h3
    unfold cj at e2 e3
    unfold lamConj
    rw [e2, e3]
  have hA' : Adp1 ⊤ σ Λ (2 * m₀) x x' := by
    unfold Adp1 StarPt at hA ⊢
    rw [hl]
    rcases hA with h | ⟨h1, h2', h3', h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2', IntermediateField.mem_top, IntermediateField.mem_top, ?_, ?_⟩
      · rw [h5, hσ _ (Or.inr (by simp)) h3']
      · rw [h6, hσ _ (Or.inr (by simp)) h4]
  have h := phase_top D hS hW cc δ hc σ hK' x x' m₀ hm hx hA'
  rw [← hΛ, hl, hσ _ (Or.inr (by simp)) he] at h
  exact h

theorem galPh1_all : ∀ D : D7, galPh1 D := fun D =>
  galPh1_of D (_root_.GlobalTheory.ConjPoint.galStar_holds D) (_root_.GlobalTheory.WeilPairingGalois.weilPairingGalois_all D)

end GlobalTheory.QuadPhase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactCoverUnHcModuleFiniteDimIrreducible
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CompactCoverIrr

theorem isKC_of_compact {n : ℕ} (X : Mat n 0) : IsKC X := by
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

theorem map_stable {n : ℕ} (hn : 1 ≤ n) (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (hj : IsHCMod τ M j) (N : Submodule ℂ M.V) [FiniteDimensional ℂ N]
    (hN : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N) (g : T.G) : ∀ x ∈ N.map j, τ.π g x ∈ N.map j := by
  have hg := GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T g (isKC_of_compact _)
  have key : (∀ x ∈ N.map j, τ.π g x ∈ N.map j) ∧ (∀ x ∈ N.map j, τ.π g⁻¹ x ∈ N.map j) := by
    induction hg using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨X, ⟨hX, -⟩, rfl⟩ := hk
      have hf := GlobalTheory.RealPar.flow_mem_map j (M.act X) N (hN X) (fun t => τ.π (T.expt (t • X)))
        (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (hj.2.2 X hX)
      have hinv : (T.expt X)⁻¹ = T.expt ((-1 : ℝ) • X) := by
        have h := T.expt_add X hX 1 (-1)
        rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at h
        exact (eq_inv_of_mul_eq_one_right h.symm).symm
      refine ⟨?_, ?_⟩
      · have := hf 1
        rwa [one_smul] at this
      · rw [hinv]
        exact hf (-1)
    | one => refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simpa using hx
    | mul a b _ _ ha hb =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [map_mul]
        exact ha.1 _ (hb.1 x hx)
      · rw [mul_inv_rev, map_mul]
        exact hb.2 _ (ha.2 x hx)
    | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩
  exact key.1

theorem eq_bot_or_top {n : ℕ} (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (hτ : IrrU τ) (hj : Function.Injective j) (N : Submodule ℂ M.V) [FiniteDimensional ℂ N]
    (hN : ∀ g, ∀ x ∈ N.map j, τ.π g x ∈ N.map j) : N = ⊥ ∨ (N = ⊤ ∧ N.map j = ⊤) := by
  rcases hτ.2 (N.map j) (Submodule.closed_of_finiteDimensional _) hN with h | h
  · left
    apply Submodule.map_injective_of_injective hj
    rw [h, Submodule.map_bot]
  · right
    refine ⟨?_, h⟩
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, hwv⟩ : j v ∈ N.map j := h ▸ Submodule.mem_top
    exact hj hwv ▸ hw

theorem hcMod_finite_irr : ∀ (n : ℕ), 1 ≤ n → ∀ (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H), IrrU τ → IsHCMod τ M j → Nontrivial M.V → FiniteDimensional ℂ M.V ∧ IrrGK M ∧ (∀ h v, ∃ v', j v' = τ.π h (j v)) ∧ ∀ N : Submodule ℂ M.V, (∀ h, ∀ v ∈ N, ∀ v', j v' = τ.π h (j v) → v' ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n hn T τ M j hτ hj hM
  obtain ⟨v, hv⟩ := exists_ne (0 : M.V)
  obtain ⟨W, hWf, hvW, hWs⟩ := M.kfin v
  have hW := (eq_bot_or_top T τ M j hτ hj.1 W
    (map_stable hn T τ M j hj W fun Z => hWs Z (isKC_of_compact Z))).resolve_left
    (fun h => hv (by rw [h] at hvW; exact hvW))
  have hfin : FiniteDimensional ℂ M.V := by
    rw [hW.1] at hWf
    exact Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule ℂ M.V) ≃ₗ[ℂ] M.V)
  have hsurj : ∀ x, ∃ v', j v' = x := fun x => by
    obtain ⟨w, -, hw⟩ : x ∈ W.map j := hW.2 ▸ Submodule.mem_top
    exact ⟨w, hw⟩
  refine ⟨hfin, ⟨hM, fun N hN => ?_⟩, fun h v => hsurj _, fun N hN => ?_⟩
  · exact (eq_bot_or_top T τ M j hτ hj.1 N (map_stable hn T τ M j hj N hN)).imp_right And.left
  · refine (eq_bot_or_top T τ M j hτ hj.1 N ?_).imp_right And.left
    rintro g _ ⟨w, hw, rfl⟩
    obtain ⟨v', hv'⟩ := hsurj (τ.π g (j w))
    exact ⟨v', hN g w hw v' hv', hv'⟩

end GlobalTheory.CompactCoverIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeSelfDualStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedStandardAdelicLattice_selfDual : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), SelfDual (gamA ψ) (latA D cc N N') := by
  first | exact @GlobalTheory.FinWeil.LatSelfDual.latA_selfDual | exact GlobalTheory.FinWeil.LatSelfDual.latA_selfDual | (intros; apply GlobalTheory.FinWeil.LatSelfDual.latA_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaDoubleTranslateMulStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.U1_two_mul_th0_mul_th0_eq : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ s, s ∉ Λ → ∀ z, U1 Λ s (sgStar Λ) 0 ^ 2 * (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) z * GL3Theta.th0 Λ t₀ z) = U1 Λ s (sgStar Λ) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) z ^ 2 + (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) 0 - U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 4) * U1 Λ s (sgStar Λ) z ^ 2 := by
  first | exact @GlobalTheory.EvenTheta.Double.evenTheta_double_translate_mul | exact GlobalTheory.EvenTheta.Double.evenTheta_double_translate_mul | (intros; apply GlobalTheory.EvenTheta.Double.evenTheta_double_translate_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaEqProdSigmaStarSquareQuotientStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 1 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ) ∧ ∀ z, F z = ∏ i, sqTh Λ (Q i) z := by
  first | exact @GlobalTheory.EvenTheta.exists_eq_prod_sqTh | exact GlobalTheory.EvenTheta.exists_eq_prod_sqTh | (intros; apply GlobalTheory.EvenTheta.exists_eq_prod_sqTh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTranslateSqEqSigmaStar
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem IsLat.evenTheta_translate_sq_eq_sigmaStar : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ t, t ∉ Λ → ∀ z, U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (GL3Theta.th0 Λ t₀) z ^ 2 = -(U1 Λ (2 * t) (sgStar Λ) z * sgStar Λ z) + (wpF Λ t - wpF Λ t₀) * U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (sgStar Λ) z ^ 2 := by
  intro Λ h t₀ h0 h2 t ht z
  have hsq := (GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity Λ h t₀ h0 h2).2.2.2.1 (z + t)
  have hσ := (h.sg_eq_zero t).not.2 ht
  rw [h.sqTh_sub h0 ht] at hsq
  have hs : sqTh Λ t (z + t) * sgStar Λ t ^ 2 = -(sgStar Λ (z + 2 * t) * sgStar Λ z) := by
    rw [sqTh, div_mul_cancel₀ _ (pow_ne_zero 2 hσ), show t - (z + t) = -z by ring, h.sg_neg,
      show t + (z + t) = z + 2 * t by ring]
    ring
  simp only [U1, zero_add, mul_pow]
  rw [hsq]
  have he : Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) (2 * t) / ↑(area Λ) -
        ↑Real.pi * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * ↑(area Λ))) =
      Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 *
      Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 := by
    rw [← mul_pow, ← Complex.exp_add, sq, ← Complex.exp_add, map_mul, map_ofNat]
    congr 1
    ring
  rw [he]
  generalize Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = a
  generalize Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = b
  linear_combination a ^ 2 * b ^ 2 * hs

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralSeriesOfCommonDivisorLineProductsStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_series_of_common_divisor_line_products : ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (e Ψ A B : PowerSeries ℂ_[p]) (y : Fin m → ℂ_[p]) (y' : Fin n → ℂ_[p]), BddSer e → BddSer Ψ → BddSer A → BddSer B → PowerSeries.constantCoeff Ψ = 1 → Ψ * A = (∏ i, lineSer e (y i)) ^ 2 → Ψ * B = ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → IntSer Ψ := by
  first | exact @GlobalTheory.EvenTheta.intSer_of_common_divisor | exact GlobalTheory.EvenTheta.intSer_of_common_divisor | (intros; apply GlobalTheory.EvenTheta.intSer_of_common_divisor <;> assumption)
end

