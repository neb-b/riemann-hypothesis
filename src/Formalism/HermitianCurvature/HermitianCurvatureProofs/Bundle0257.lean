module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0254
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0235
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0253
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0230
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0226
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffExists
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cutoff_exists {H : B.Mat k n → (Wq →L[ℂ] Wp)} (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ) (hi : i ≤ n)
    (hL : ∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g) {Cs : Set (B.Mat k n)}
    (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) {c0 : ℂ} (hc0 : c0 ≠ 0) :
    ∃ Ht : B.Mat k n → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k n) Ht ∧ (∀ g ∈ B.GV k n, g ∉ Cs → Ht g = 0) ∧
      ∀ g ∈ B.GV k n, dist (Dmin k n z z' g ⟨i, by omega⟩) c0 < ‖c0‖ / 4 → Ht g = H g := by
  set l : Fin (n + 2) := ⟨i, by omega⟩ with hl
  have hc : 0 < ‖c0‖ := norm_pos_iff.mpr hc0
  obtain ⟨χD, ⟨hχs, -, -⟩, hχ1, hχsupp⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc0
  have hDc : Continuous (fun g : B.Mat k n => Dmin k n z z' g l) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l).continuous
  refine ⟨fun g => χD (Dmin k n z z' g l) • H g, ?_, ?_, ?_⟩
  · intro g0 hg0
    by_cases hmem : Dmin k n z z' g0 l ∈ tsupport χD
    · have hne : Dmin k n z z' g0 l ≠ 0 := by
        intro h0
        have := (hχsupp _ hmem).1
        rw [h0, norm_zero] at this
        linarith
      obtain ⟨U, f', hU, hgU, hf', he⟩ := hL g0 hg0 hne
      refine ⟨U, fun g => χD (Dmin k n z z' g l) • f' g, hU, hgU, ?_, fun g hg hgG => ?_⟩
      · exact ((hχs.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l)).contDiffOn).smul hf'
      · show χD (Dmin k n z z' g l) • H g = χD (Dmin k n z z' g l) • f' g
        rw [he g hg hgG]
    · refine ⟨(fun g => Dmin k n z z' g l) ⁻¹' (tsupport χD)ᶜ, fun _ => 0,
        (isClosed_tsupport χD).isOpen_compl.preimage hDc, hmem, contDiffOn_const, fun g hg _ => ?_⟩
      show χD (Dmin k n z z' g l) • H g = 0
      rw [image_eq_zero_of_notMem_tsupport hg, zero_smul]
  · intro g hg hgC
    show χD (Dmin k n z z' g l) • H g = 0
    rw [hS g hg hgC, smul_zero]
  · intro g _ hd
    show χD (Dmin k n z z' g l) • H g = H g
    rw [hχ1 _ (le_of_lt hd), one_smul]

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Hpart1SingleEs
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section star

variable {k r j : ℕ}

theorem hpart1_single_es (hj : j + 1 ≤ r) (b : Fin j) :
    hpart1 (Hpk k r) (Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (-1 / 2) := by
  unfold hpart1 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_esI, single_mul_hpk_esI]
  have h2 : star (-1 / 2 : ℂ) = -1 / 2 := by
    rw [star_div₀, star_neg, star_one, star_ofNat]
  rw [h2, show (-1 / 2 : ℂ) = -(1 / 2) by ring, neg_smul, neg_smul, sub_neg_eq_add, smul_sub]
  change (1 / 2 : ℂ) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ) -
      (1 / 2 : ℂ) • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ) =
    -((1 / 2 : ℂ) • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) +
      (1 / 2 : ℂ) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)
  abel

theorem hpart2_single_es (hj : j + 1 ≤ r) (b : Fin j) :
    hpart2 (Hpk k r) (Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / (2 * Complex.I)) := by
  unfold hpart2 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_esI, single_mul_hpk_esI,
    smul_add]
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp [Complex.conj_I]
  rw [h2, neg_smul, sub_neg_eq_add]
  change (1 / (2 * Complex.I)) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ) +
      (1 / (2 * Complex.I)) • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ) =
    (1 / (2 * Complex.I)) • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ) +
      (1 / (2 * Complex.I)) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)
  abel

end star

end Formalism.FourierDecayAlt.P.LevelPointCoordinates

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem star_rule_x0 : CutHL.ConjugateActionRuleAtBasePoint := by
  intro E _ _ k r j hj z Dm Ψ Z τ γ hj1 hz hD hS hZ hτ hγ hx hEq b
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_single_es hj b, hpart2_single_es hj b, rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b,
    rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b, smul_smul, ← add_smul, ← map_mul]
  congr 1
  set w := τ * Z⁻¹ b ⟨j - 1, by omega⟩
  have e1 : (-1 / 2 : ℂ) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = -w / 2 := by simp only [w]; ring
  have e2 : 1 / (2 * Complex.I) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = -(Complex.I * w) / 2 := by
    simp only [w]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  simp only [map_div₀, map_neg, map_mul, Complex.conj_I, map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperLeftVariablesDomain
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

def ProperLeftVariablesDomain : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (PBQ.domP P.k P.r j p.T.base.z p.T.base.z')

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceIntN (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hset : {x | x ∈ B.GV k (p + ρ) ∧ Dmin k (p + ρ) B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} =
      {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    ext x
    show _ ∧ _ ↔ _ ∧ _
    rw [Formalism.FourierDecayAlt.P.hat_z_minimum_degree k p ρ B0.z B0.z' x]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := hset ▸ hHc
  have h := (Formalism.FourierDecayAlt.P.slice_integral_jacobian_factor hp σ d hd Bj B0 hz'.symm hπ'' hW' hW0' hNj hN0 g hg H hHc' R hR).2
  have hF : D.castF (rfl : p + ρ = p + ρ) H = H := funext fun y => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hV : ∀ v : Fin (2 * (p + ρ) + k + 1) → ℂ, D.castV (rfl : p + ρ = p + ρ).symm v = v :=
    fun v => Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl v
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, hF, hV, ← hz, ← hz']
  exact h

end gen

section pt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem slice_eq {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (H : B.Mat k r → E) (a : C.LPt) (hle : D.ptSize a ≤ r)
    (h2 : r - D.ptSize a = r - D.ptSize a) (e : D.ptSize a + (r - D.ptSize a) = r) :
    D.castF h2 (D.sliceAt k r z z' H a) =
      U.PhiFun (s := 0) k (r - D.ptSize a) (D.ptPerm a) (D.ptDiag a) (D.castV e.symm z) (D.castV e.symm z')
        (D.castF e H) (fun a => a.elim0) := by
  funext y
  unfold D.castF
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, D.sliceAt, dite_eq_left hle]
  rfl

theorem mMap_castM {k j a b : ℕ} (h : a = b) (Z : Matrix (Fin j) (Fin j) ℂ) (g : B.Mat k a) :
    U.mMap k j b Z (D.castM h g) = D.castM (by omega : j + a = j + b) (U.mMap k j a Z g) := by
  subst h
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem pt_eq {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det) (τ : ℂ) (hτ : τ ≠ 0)
    (γ : B.Mat k (r - (j + 1))) (e0 : j + (r - j) = r) (h1 : 1 + (r - (j + 1)) = r - j) :
    D.castM e0 (U.mMap k j (r - j) Z (D.castM h1 (U.mMap k 1 (r - (j + 1)) (Matrix.of fun _ _ => τ) γ))) =
      LevelPointCoordinates.x0 k r j hj Z τ γ := by
  rw [mMap_castM, Formalism.FourierDecayAlt.P.PBH.asm_castM_castM]
  unfold LevelPointCoordinates.x0 LevelPointCoordinates.zfull
  have hM : D.castM (Formalism.FourierDecayAlt.P.PBH.hs' k j (r - (j + 1)))
      (U.mMap k j (1 + (r - (j + 1))) Z (U.mMap k 1 (r - (j + 1)) (Matrix.of fun _ _ => τ) γ)) =
      U.mMap k (j + 1) (r - (j + 1)) (U.blk2 Z 0 0 (Matrix.of fun _ _ => τ)) γ :=
    Formalism.FourierDecayAlt.P.PBH.M2 (k := k) (ρ := r - (j + 1)) Z hZ τ hτ γ
  rw [← hM, Formalism.FourierDecayAlt.P.PBH.asm_castM_castM]

end pt

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveOperatorLeL2Subspace
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem opClos_le {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (X : ActualOps k r z z' π π') (l : Fin r)
    {B V : Submodule ℂ (RadSp k r z z' π π')} (hB : B ≤ V) (hV : ∀ (j : Fin 6), ∀ Φ ∈ V, X.op l j Φ ∈ V) :
    OpClos X l B ≤ V := by
  rw [OpClos, Submodule.span_le]
  rintro Φ ⟨js, Ψ, hΨ, rfl⟩
  show (js.map (X.op l)).prod Ψ ∈ V
  induction js with
  | nil => simpa using hB hΨ
  | cons j js ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact hV j _ ih

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain in
theorem wave_operator_le_l2_subspace (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq)
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) :
    waveJ P z z' π π' D l ≤ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine Submodule.span_le.mpr fun Ψ hΨ => ?_
  obtain ⟨s, ε, G, Φ, Wv, -, hN, hlc, hΦ, hWv, rfl⟩ := unwave P z z' π π' D l Ψ hΨ
  refine unimodular_multiplier_preserves_L2 μ hμ hWv (fun _ _ => norm_fsv _ _) Φ ⟨hlc, fun c => ?_⟩
  subst hz hz' hπ hπ'
  have h := level_zero_form_integrable_compact (S := Empty) D μ hμ (fun _ => G) (fun _ => G) (fun _ => Φ) (fun _ => Φ)
    (fun _ => hN.2.1) (fun _ => hN.2.1) (fun _ => hΦ) (fun _ => hΦ) c
  unfold LevelZeroSquareIntegrable
  simpa [wt0] using h

end Wave

end Formalism.FourierDecayAlt.P.CutSE
end
end

