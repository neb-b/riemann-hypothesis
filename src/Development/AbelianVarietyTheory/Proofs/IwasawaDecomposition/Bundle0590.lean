module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HermitianLattices.StatementLat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem dvd_of_exp_eq_one (k : ℤ) (N : ℕ) (hN : 0 < N)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (k : ℂ) / N) = 1) : (N : ℤ) ∣ k := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_eq_iff hN'] at hm
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : (2 * Real.pi * Complex.I) * ((k : ℂ) + m * N) = 0 := by linear_combination -hm
  have h4 : ((k + m * N : ℤ) : ℂ) = 0 := by push_cast; exact (mul_eq_zero.1 h3).resolve_left hpi
  have h5 : k + m * N = 0 := by exact_mod_cast h4
  exact ⟨-m, by linarith⟩

theorem eq_of_exp_eq (m m' : ℤ) (h : ∀ N : ℕ, 0 < N → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / N) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (m' : ℂ) / N)) : m = m' := by
  have hN : 0 < (m - m').natAbs + 1 := Nat.succ_pos _
  have h1 := h _ hN
  have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (((m - m' : ℤ)) : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ)) = 1 := by
    have e : -(2 * Real.pi * Complex.I) * (((m - m' : ℤ)) : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) =
        -(2 * Real.pi * Complex.I) * (m : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) -
          -(2 * Real.pi * Complex.I) * (m' : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 := dvd_of_exp_eq_one _ _ hN h2
  have h4 : m - m' = 0 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [Int.abs_eq_natAbs]; push_cast; omega)
  omega

theorem hermForm_im_sum (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (x y : Fin r → ℤ) :
    (hermForm Hm (∑ j, x j • lam j) (∑ j, y j • lam j)).im =
      ∑ i, ∑ j, (x i : ℝ) * (y j : ℝ) * (hermForm Hm (lam i) (lam j)).im := by
  have hs : ∀ (k : ℤ) (v : Fin g → ℂ), k • v = (k : ℂ) • v := fun k v => (Int.cast_smul_eq_zsmul ℂ k v).symm
  simp only [hermForm, hs, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, star_intCast, Finset.mul_sum, Complex.im_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem logDom_facts (n a : ℕ) : IsOpen (logDom n a) ∧ Convex ℝ (logDom n a) ∧
    (∀ s, AnalyticAt ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧
    Set.MapsTo (logExp a) (logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) :=
  _root_.GlobalTheory.logDom_chart_props n a

theorem logExp_ne_zero (n a : ℕ) (s : Fin n → ℂ) (k : Fin n) (hk : (k : ℕ) < a) : logExp a s k ≠ 0 := by
  simp [logExp, hk, Complex.exp_ne_zero]

theorem isLatFam_comp (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) : IsLatFam B K → IsOpen B' →
    AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B → IsLatFam B' (fun b => K (φ b)) :=
  _root_.GlobalTheory.ShFam.Hor.LogCh.IsLatFam.pullback_analytic m n g B B' K φ

theorem det_ne_zero_of_herm (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ)
    (M : Matrix (Fin r) (Fin r) ℤ) : (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ lam →
    Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 :=
  _root_.GlobalTheory.det_ne_zero_of_im_hermForm_eq_int g r Hm lam M

theorem linIndep_rows (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) :
    LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) :=
  _root_.GlobalTheory.rowsInd_rat_of_real g r r₀ lam u A

theorem bounded_span (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ)
    (A : Fin r₀ → Fin r → ℤ) (C : ℝ) : (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) →
    ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' :=
  _root_.GlobalTheory.combo_of_bounded_rows_bounded X g r r₀ T lam u A C

theorem mem_of_isLatBasis {g r : ℕ} {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (h : IsLatBasis K b) (i : Fin r) :
    b i ∈ K :=
  (h.2 (b i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩

theorem span_top_of_isLatBasis {g r : ℕ} {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (h : IsLatBasis K b)
    (hK : Submodule.span ℝ K = ⊤) : Submodule.span ℝ (Set.range b) = ⊤ := by
  rw [eq_top_iff, ← hK, Submodule.span_le]
  intro w hw
  obtain ⟨m, rfl⟩ := (h.2 w).1 hw
  exact Submodule.sum_mem _ fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := b) j)) _

end GlobalTheory.ShFam.Hor.LogCh.Core

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem core : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ (∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r₀ K ζ Pair hK hζan hζli hζK hζ0 hζbd hstd huniq hprop hinner hS
  obtain ⟨hDo, hDc, hEa, hEm⟩ := logDom_facts n a
  have hDp : IsPreconnected (logDom n a) := hDc.isPreconnected
  have hEd : Differentiable ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) := fun s => (hEa s).differentiableAt
  have hK' : IsLatFam (logDom n a) (fun s => K (logExp a s)) :=
    isLatFam_comp n n g _ _ K (logExp a) hK hDo (fun s _ => hEa s) hEm
  have hin := fun s (hs : s ∈ logDom n a) => hinner _ (hEm hs) (fun k hk => logExp_ne_zero n a s k hk)
  obtain ⟨lam, hlamD, hlamB⟩ := GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex n g (2 * g) (logDom n a) (fun s => K (logExp a s)) hDo hDc
    (fun s hs => _root_.GlobalTheory.ShFam.Hor.LogCh.IsLatFam.exists_analytic_locBasis n g (logDom n a) (fun s => K (logExp a s)) s hK' hs (hin s hs).choose_spec.2.2.1)
  have hmem : ∀ s ∈ logDom n a, ∀ i, lam s i ∈ K (logExp a s) := fun s hs i => mem_of_isLatBasis (hlamB s hs) i
  have hlamDi : ∀ i, DifferentiableOn ℂ (fun s => lam s i) (logDom n a) := fun i => differentiableOn_pi.1 hlamD i
  let s₀ : Fin n → ℂ := fun _ => (-1 / 2 : ℂ)
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    split_ifs <;> norm_num [s₀]
  obtain ⟨Hm₀, -, hpos₀, hspan₀, hint₀, hpair₀⟩ := hin s₀ hs₀
  have hMex : ∀ i j, ∃ m : ℤ, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = m := fun i j =>
    hint₀ _ (hmem s₀ hs₀ i) _ (hmem s₀ hs₀ j)
  obtain ⟨M, hM₀⟩ : ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ, ∀ i j, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = M i j :=
    ⟨fun i j => (hMex i j).choose, fun i j => (hMex i j).choose_spec⟩

  have hM : ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) →
      (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) →
        Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
          (Complex.exp_ne_zero _))) →
      ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j := by
    intro s hs Hm hint hpair i j
    obtain ⟨m', hm'⟩ := hint _ (hmem s hs i) _ (hmem s hs j)
    have key : m' = M i j := by
      apply eq_of_exp_eq
      intro N hN
      have h1 := hpair₀ N _ _ hN (hmem s₀ hs₀ i) (hmem s₀ hs₀ j)
      have h2 := hprop n N (logDom n a) (logExp a) (fun s => lam s i) (fun s => lam s j) _ s₀ s hN hDo hDp
        hEd.differentiableOn hEm (hlamDi i) (hlamDi j) (fun b hb => ⟨hmem b hb i, hmem b hb j⟩) hs₀ hs h1
      have h3 := hpair N _ _ hN (hmem s hs i) (hmem s hs j)
      have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
      simp only [Units.val_mk0, hm', hM₀, Complex.ofReal_intCast] at h4
      exact h4
    rw [hm', key]

  have hstdK : ∀ j : Fin g, ∀ s ∈ logDom n a, (Pi.single j 1 : Fin g → ℂ) ∈ K (logExp a s) := by
    intro j s hs
    obtain ⟨i, hi⟩ := hstd j
    rw [← hi _ (hEm hs)]
    exact hζK _ (hEm hs) i
  have hρex : ∀ j : Fin g, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a,
      (Pi.single j 1 : Fin g → ℂ) = ∑ k, m k • lam s k := fun j =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun _ => Pi.single j 1) s₀ hDp
      hlamD.continuousOn continuousOn_const hlamB (fun s hs => hstdK j s hs) hs₀
  choose mρ hmρ using hρex

  have hζc : ContinuousOn ζ (Metric.ball 0 1) := hζan.continuousOn
  have hζEc : ∀ i, ContinuousOn (fun s => ζ (logExp a s) i) (logDom n a) := fun i =>
    (continuousOn_pi.1 (hζc.comp hEd.continuous.continuousOn hEm)) i
  have hAex : ∀ i, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a, ζ (logExp a s) i = ∑ k, m k • lam s k := fun i =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun s => ζ (logExp a s) i) s₀ hDp
      hlamD.continuousOn (hζEc i) hlamB (fun s hs => hζK _ (hEm hs) i) hs₀
  choose A hA using hAex

  have hz₁ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := hEm hs₀
  have hsumK : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ z j ∈ K z := by
    intro z hz c
    obtain ⟨H, hH⟩ := hK.2.1 z hz
    have hj : ∀ j, ζ z j ∈ H := fun j => by rw [← SetLike.mem_coe, hH]; exact hζK z hz j
    rw [← hH]
    exact H.sum_mem fun j _ => H.zsmul_mem (hj j) _
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζan.differentiableOn
  have hsumD : ∀ c : Fin r₀ → ℤ, DifferentiableOn ℂ (fun z => ∑ j, c j • ζ z j) (Metric.ball 0 1) := by
    intro c
    have h : ∀ j ∈ (Finset.univ : Finset (Fin r₀)), DifferentiableOn ℂ (fun z => c j • ζ z j) (Metric.ball 0 1) :=
      fun j _ => (differentiableOn_pi.1 hζd j).const_smul (c j)
    refine (DifferentiableOn.sum h).congr fun z _ => ?_
    simp [Finset.sum_apply]
  have hsum_eq : ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ (logExp a s₀) j = ∑ k, (∑ i, c i • A i) k • lam s₀ k := by
    intro c
    simp only [fun i => hA i s₀ hs₀, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hform : ∀ x y : Fin (2 * g) → ℤ, (hermForm Hm₀ (∑ k, x k • lam s₀ k) (∑ k, y k • lam s₀ k)).im =
      ((x ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ y : ℤ) : ℝ) := by
    intro x y
    rw [hermForm_im_sum]
    simp only [hM₀, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ c c' : Fin r₀ → ℤ, (fun j => (c j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, c i • A i) ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ (∑ i, c' i • A i) := by
    intro N hN
    obtain ⟨S, hcard, hSp⟩ := hS N hN
    refine ⟨S, hcard, fun c c' hc => ?_⟩
    have h1 := hSp c c' hc
    have h2 := hprop n N (Metric.ball 0 1) id (fun z => ∑ j, c j • ζ z j) (fun z => ∑ j, c' j • ζ z j) 1 0
      (logExp a s₀) hN Metric.isOpen_ball (convex_ball 0 1).isPreconnected differentiableOn_id (Set.mapsTo_id _)
      (hsumD c) (hsumD c') (fun b hb => ⟨hsumK b hb c, hsumK b hb c'⟩) (Metric.mem_ball_self one_pos) hz₁ h1
    have h3 := hpair₀ N _ _ hN (hsumK _ hz₁ c) (hsumK _ hz₁ c')
    have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
    simp only [Units.val_mk0, Units.val_one, id, hsum_eq, hform, Complex.ofReal_intCast] at h4
    exact dvd_of_exp_eq_one _ N hN h4
  have hdet : (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ).det ≠ 0 :=
    det_ne_zero_of_herm g (2 * g) Hm₀ (lam s₀) M hpos₀ (hlamB s₀ hs₀).1
      (span_top_of_isLatBasis (hlamB s₀ hs₀) hspan₀) hM₀
  have hlinQ := linIndep_rows g (2 * g) r₀ (lam s₀) (ζ (logExp a s₀)) A (hζli _ hz₁) (fun i => hA i s₀ hs₀)
  have hco := GlobalTheory.T.coisotropic_sublattice_of_torsion_count (2 * g) r₀ M A hdet hlinQ hdvd

  obtain ⟨C, hC⟩ := hζbd
  have hgr := _root_.GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic n a g (2 * g) lam ((M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ).map (Int.cast : ℤ → ℝ))
    (Submodule.span ℝ (Set.range fun i j => (A i j : ℝ))) hlamD
    (fun s hs => by
      obtain ⟨Hm, hH, hpos, hspan, hint, hpair⟩ := hin s hs
      exact ⟨(hlamB s hs).1, span_top_of_isLatBasis (hlamB s hs) hspan, Hm, hH, hpos, fun i j => by
        rw [hM s hs Hm hint hpair i j]; simp⟩)
    (fun v hv => hco v fun i => hv _ (Submodule.subset_span (Set.mem_range_self (f := fun i j => (A i j : ℝ)) i)))
    (fun w hw => by
      obtain ⟨C', hC'⟩ := bounded_span (Fin n → ℂ) g (2 * g) r₀ (logDom n a) lam (fun s => ζ (logExp a s)) A C
        (fun s hs i => hA i s hs) (fun s hs => hC _ (hEm hs)) w hw
      exact ⟨C', fun s hs _ => hC' s hs⟩)
  refine ⟨2 * g, lam, fun j k => (mρ j k : ℂ), hlamD.continuousOn,
    fun s hs => ⟨(hlamB s hs).1.restrict_scalars' ℤ, (hlamB s hs).2, fun j => ?_⟩, hgr⟩
  rw [hmρ j s hs]
  exact Finset.sum_congr rfl fun k _ => Int.cast_smul_eq_zsmul ℂ _ _

end GlobalTheory.ShFam.Hor.LogCh.Core
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauShift

open GlobalTheory.PsiTauCoordRel GlobalTheory.PeriodBalance GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev cK (ξ : Spec (CommRingCat.of (FractionRing R))) : Rˣ →* ((TK R).left.presheaf.stalk ξ)ˣ :=
  Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom

abbrev kK (ξ : Spec (CommRingCat.of (FractionRing R))) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk ξ)ˣ :=
  Units.map (kst ξ).toMonoidHom

variable [IsLocalRing R]

theorem coord_val (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    ∃ u : Rˣ, Units.map (kst ξ).toMonoidHom x =
      cK ξ u * val (D.tau a b) (𝟙 (TK R).left) ξ J := by
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom
  obtain ⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 (TK R).left) ξ J = cU w := by
    unfold DegPre.rigK
    rw [val_pull hJ]
    have : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
    rw [this]
    exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]
  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau a b) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc (a + b) _ i1 (mem_inl (mem_inl (mem_inl hm)))
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc a _ i2 (mem_inr (mem_inl (mem_inl hm)))
  obtain ⟨c3, g3⟩ := val_psi_chart D ξ hJ hJc b _ i3 (mem_inr (mem_inl hm))
  obtain ⟨c4, g4⟩ := gm_rigK D ξ _ i4 (mem_inr hm)
  have vt := GlobalTheory.PeriodBalance.val_tau D ξ hJ a b
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) =
      Units.map (kst ξ).toMonoidHom (genVal (D.tau a b) j h) := Units.ext eT
  refine ⟨c1⁻¹ * c2 * c3 * c4⁻¹ * c5, ?_⟩
  rw [← eT', dT, g4, vt, g1, g2, g3, h5]
  simp only [cU, map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_add (D : DegPre R) (hB : D.TauBimult) (ξ : Spec (CommRingCat.of (FractionRing R))) {J}
    (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (D.tau (a + a') b) (𝟙 (TK R).left) ξ J = cK ξ w *
      (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau a' b) (𝟙 (TK R).left) ξ J) := by
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 (TK R).left)).trans (val_mul hJ _ _ _))
  rw [val_pull (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) hJ D.cub.t (D.pt3 a a' b)] at e
  have hp : 𝟙 (TK R).left ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp] at e
  obtain ⟨w, hw⟩ := val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t (lift (D.c a) (lift (D.c a') (D.c b))).left fun k => by
    show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) k.down).left) ≫ D.P.A.hom = 𝟙 _
    rw [Category.assoc, Over.w, Over.w]; rfl
  refine ⟨w⁻¹, ?_⟩
  have hw' : val D.cub.t (jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left) ξ J = cK ξ w := hw
  rw [← e, map_inv, eq_inv_mul_iff_mul_eq, mul_comm]
  exact congrArg _ hw'.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  intro R _ _ _ D hB a z b k x x' x'' hx hx' hx''
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  have hind : ∀ n : ℕ, ∃ w : Rˣ, val (D.tau (a + n • z) b) (𝟙 (TK R).left) ξ J =
      cK ξ w * (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau z b) (𝟙 (TK R).left) ξ J ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨1, by rw [zero_nsmul, add_zero, map_one, pow_zero, _root_.one_mul, _root_.mul_one]⟩
    | succ n ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ := val_add D hB ξ hJ hJc (a + n • z) z b
      refine ⟨w' * w, ?_⟩
      rw [succ_nsmul, ← add_assoc, hw', hw, map_mul, pow_succ]
      ac_rfl
  obtain ⟨w, hw⟩ := hind k
  obtain ⟨u1, e1⟩ := coord_val D ξ hJ hJc hx
  obtain ⟨u2, e2⟩ := coord_val D ξ hJ hJc hx'
  obtain ⟨u3, e3⟩ := coord_val D ξ hJ hJc hx''
  refine ⟨u3 * w * u1⁻¹ * (u2⁻¹) ^ k, ?_⟩
  apply Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ)
  show kK ξ x'' = kK ξ _
  replace e1 : kK ξ x = _ := e1
  replace e2 : kK ξ x' = _ := e2
  replace e3 : kK ξ x'' = _ := e3
  have hc : ∀ v : Rˣ, kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom v) =
      cK ξ v := fun v => Units.ext rfl
  have f1 : val (D.tau a b) (𝟙 (TK R).left) ξ J = cK ξ u1⁻¹ * kK ξ x := by
    rw [e1, map_inv, inv_mul_cancel_left]
  have f2 : val (D.tau z b) (𝟙 (TK R).left) ξ J = cK ξ u2⁻¹ * kK ξ x' := by
    rw [e2, map_inv, inv_mul_cancel_left]
  rw [map_mul, hc, map_mul, map_pow, e3, hw, f1, f2]
  simp only [map_mul, map_inv, map_pow, mul_pow]
  ac_rfl

end GlobalTheory.TauShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataNonzeroIndexPlacesCorrespond
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem exists_hom_of_range {K K' : Type} [Field K] [Field K'] (σ : K →+* ℂ) (σ' : K' →+* ℂ) (h : Set.range σ ⊆ Set.range σ') :
    ∃ φ : K →+* K', ∀ x, σ' (φ x) = σ x := by
  choose g hg using fun x => h ⟨x, rfl⟩
  exact ⟨{ toFun := g
           map_one' := σ'.injective (by rw [hg, map_one, map_one])
           map_mul' := fun a b => σ'.injective (by rw [map_mul σ', hg, hg, hg, map_mul])
           map_zero' := σ'.injective (by rw [hg, map_zero, map_zero])
           map_add' := fun a b => σ'.injective (by rw [map_add σ', hg, hg, hg, map_add (f := _)]) }, hg⟩


set_option maxHeartbeats 4000000 in
theorem extendedData_nonzero_index_places_correspond : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (_root_.GlobalTheory.Mem.R3.LiftLat0.liftFormsLattice_definiteLattice_baseChange_extended_alt h1 h2 h3 h4 h5 h6 h7) (_root_.GlobalTheory.Mem.R3.TwistedPlaceExtensions.defLat0_baseChange h1 h2 h3 h4 h5 h6 h7)) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ hIJ B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt v v' hB
  have hm : (w.st Z).toD7.R.m = (w'.st Z').toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1.symm
  obtain ⟨φ, hφ⟩ := exists_hom_of_range (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL hE.2.2.2
  have hok := hHL.ok.ok2
  refine mem_zeroContentPlaces_iff_over_of_nonvanishing z z' hm (fun j j' hj P P' hPP => ?_) v v' hB
  have hP : ∀ (x : 𝓞 (w.st Z).toD7.what₂.LL) (x' : 𝓞 (w'.st Z').toD7.what₂.LL), φ (x : (w.st Z).toD7.what₂.LL) = (x' : (w'.st Z').toD7.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal) := fun x x' e => hPP x x' (by rw [← e, hφ])
  have hT : Submodule.IsLattice (w.st Z).toD7.what₂.LL (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) := Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr
  have hTfull : Submodule.IsFullLattice (w.st Z).toD7.what₂.LL (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) :=
    Formalism.L2.DIV.BlockDat.Tl_full hok.conj (hok.lifts j _) hok.irr
  have hH : IsUnit (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).det := Formalism.L2.DIV.BlockDat.HZ_det hok.conj (hok.lifts j _) hok.irr
  obtain ⟨G, hG1, hG2, hG3⟩ := hIJ.1 B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨N, hN1, hN2, hN3⟩ := hIJ.2 B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  refine nzAt_iff_of z z' j j' P P' ?_ ?_
  · have k := _root_.GlobalTheory.LidxBaseChange.lidx_ne_zero_iff _ _ φ _ _ G hG1 P P' hP ((s0Of z.R z.F).M j)
      (Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (hHL.mLat j).fg (hT.fg.map _)
    rw [← hG2, ← hG3] at k
    exact k
  · have k := _root_.GlobalTheory.LidxBaseChange.lidx_ne_zero_iff _ _ φ _ _ N hN1 P P' hP _ _ hT.fg (GlobalTheory.Mem.NonzeroPlacesOverPrimes.dual_fg _ hH _ hTfull)
    rw [← GlobalTheory.Mem.DualBC.dual_baseChange _ _ φ _ _ N hN1 _ _ hN3 hH _ hTfull, ← hN2] at k
    exact k

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtraTiedCol
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Top.Bl.WPt.extraTied_col : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Forms.ColsExtraTiedS q.x.col.full q.O.ex ∧ ∃ g : Formalism.L2.G.GroupCompatibilityAll (q.w.D q.Z) q.O.gatT q.O.ex.cmp, HEq g q.x.col.g ∧ g.herm = q.x.col.full.1.to0 ∧ g.forms = fun u => (q.x.col.C.forms u).to0 := by
  intro 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, K', X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kt, div, thT, obj, ox, real,
    dsig_eq, hgauge, good⟩ := x
  obtain ⟨⟨C, std, stdLv, full, stdDt, Gt, cmp', g, herm_eq, forms_eq, gpl⟩, isRec, om⟩ := col
  dsimp only at hlev herrX ker_eq ⊢
  cases ker_eq
  exact ⟨⟨⟨hlev, herrX, gpl⟩, kt.iw, kt.iw_pos⟩, g, HEq.rfl, herm_eq, forms_eq⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaCoefficientBoundedAlongHolomorphicArcStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCoefficient_bounded_along_holomorphicArc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C := by
  first | exact @GlobalTheory.ArcNormal.theta_const_bounded | exact GlobalTheory.ArcNormal.theta_const_bounded | (intros; apply GlobalTheory.ArcNormal.theta_const_bounded <;> assumption)
end

