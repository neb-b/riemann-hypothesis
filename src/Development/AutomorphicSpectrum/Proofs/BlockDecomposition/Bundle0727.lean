module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0725
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSumBoundUniform
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0679
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0683
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0724
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0720
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0722
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0719
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0721
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0438

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictExistsPtIdealEqBot
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem dict_ptIdeal_injective {m : ℕ} (n : Fin (m + 1) → ℕ) :
    Function.Injective (ptIdeal : MP ℤ m n → Ideal (Geo.MRing (Bk n))) := fun x y h =>
  (((_root_.GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le m n x y).2 h.le).antisymm ((_root_.GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le m n y x).2 h.ge)).eq

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscriminantIdentity
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscP

theorem isoV_symm {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {V V' : Submodule ℂ (Sm E N)}
    (hV : _root_.GlobalTheory.CuspRep.IsStable V) (h : IsoV V V') : IsoV V' V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun o φ ψ e => ?_⟩
  have hm : act o (T.symm φ).1 ∈ V := hV o _ (T.symm φ).2
  have h1 := hT o (T.symm φ) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply, ← e] at h1
  have h2 : T ⟨_, hm⟩ = ψ := Subtype.ext h1
  rw [← h2, LinearEquiv.symm_apply_apply]

theorem main : FinDisc := by
  intro E _ _ _ N _ _ μ _ K W R ε hK hW hε hRep
  set D : Submodule ℂ (Sm E N) → Prop := fun V => IsDiscrete V ∧ HasType K W V ∧ InfBdd R V ∧
    ∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r)) with hD
  by_cases hne : ∃ V, D V
  swap
  · exact ⟨∅, fun V h1 h2 h3 h4 => (hne ⟨V, h1, h2, h3, h4⟩).elim⟩
  obtain ⟨V₁, h₁⟩ := hne
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt E N μ _ (h₁.1.sqInt 0 (zero_mem _))
  obtain ⟨α, δ, hαc, hαs, hδ, hα⟩ := hRep
  obtain ⟨Ω, hΩ, hconc⟩ := GlobalTheory.T.typed_space_approximation E N μ K W R ε δ α F hK hW hε hαc hαs hδ hF
  obtain ⟨B, hB, hbes⟩ := _root_.GlobalTheory.CompanionTheory.FinDisc.bessel_lintegral_le E N μ δ α F Ω hαc hαs hδ hF hΩ

  have key : ∀ (n : ℕ) (Vs : Fin n → Submodule ℂ (Sm E N)), (∀ i, D (Vs i)) →
      (∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j)) → (n : ENNReal) ≤ 2 * B := by
    intro n Vs hVs hne
    have hsel : ∀ i, ∃ ψ : Sm E N, ψ ∈ Vs i ∧ TypeB K W ψ ∧ (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 := by
      intro i
      obtain ⟨hd, ⟨φ, hφ, h0, hty⟩, -, -⟩ := hVs i
      obtain ⟨hT, hZ⟩ := _root_.GlobalTheory.CompanionTheory.FinDisc.sqMass_ne_top_and_ne_zero E N μ F hF φ (hd.aut φ hφ) (hd.sqInt φ hφ) h0
      set L := ∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ with hL
      have hLr : 0 < L.toReal := ENNReal.toReal_pos hZ hT
      set c : ℝ := (Real.sqrt L.toReal)⁻¹ with hc
      have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hLr)
      refine ⟨(c : ℂ) • φ, (Vs i).smul_mem _ hφ, ⟨fun u hu g => ?_, fun g => ?_⟩, ?_⟩
      · have := hty.1 u hu g
        simp only [Submodule.coe_smul, Pi.smul_apply, this]
      · exact W.smul_mem (c : ℂ) (hty.2 g)
      · have e : ∀ x, ‖(((c : ℂ) • φ : Sm E N)).1 x‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖φ.1 x‖ₑ ^ 2 := by
          intro x
          have h2 : ((((c : ℂ) • φ : Sm E N)).1 x) = (c : ℂ) * φ.1 x := rfl
          rw [h2, enorm_mul, mul_pow]
          congr 1
          rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0,
            ENNReal.ofReal_pow hc0.le]
        simp only [e]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hL]
        have : c ^ 2 = (L.toReal)⁻¹ := by
          rw [hc, inv_pow, Real.sq_sqrt hLr.le]
        rw [this, ENNReal.ofReal_inv_of_pos hLr, ENNReal.ofReal_toReal hT]
        exact ENNReal.inv_mul_cancel hZ hT
    choose ψ hψV hψT hψ1 using hsel
    have hcont : ∀ i, Continuous (ψ i).1 := fun i =>
      ContAut.continuous_of_isOpen_stab E N (ψ i) ((hVs i).1.aut _ (hψV i)).level
    have hleft : ∀ i, ∀ γ ∈ latticeGL E N, ∀ x, (ψ i).1 (γ * x) = (ψ i).1 x := by
      intro i γ hγ x
      obtain ⟨ρ, m, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
      have h1 := ((hVs i).1.sqInt _ (hψV i)).1
      rw [mul_assoc, ((hVs i).1.aut _ (hψV i)).left, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast, h1]
    have hs : ∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * (ψ i).1 (x * y) ∂μ = s * (ψ i).1 x := by
      intro i
      refine hα (ψ i) ((hVs i).1.aut _ (hψV i)) (hψT i) fun τ => ?_
      obtain ⟨m, hm, hb⟩ := (hVs i).2.2.1 τ
      refine ⟨m, ⟨hm.1, fun u φ hφ => ?_⟩, hb⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      rw [map_smul, hm.2 u _ (hψV i), smul_comm]
    have hcB := hbes n (fun i => (ψ i).1) hcont hleft hs hψ1 (fun i j hij =>
      _root_.GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV E N μ F hF (Vs i) (Vs j) (hVs i).1 (hVs j).1 (hne i j hij) _ (hψV i) _ (hψV j))
    have h1 : ∀ i, 1 ≤ 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := fun i =>
      hconc (Vs i) (ψ i) (hVs i).1 (hψV i) (hψT i) (hVs i).2.2.1 (hVs i).2.2.2 (hs i) (hψ1 i)
    calc (n : ENNReal) = ∑ _i : Fin n, (1 : ENNReal) := by simp
      _ ≤ ∑ i : Fin n, 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := Finset.sum_le_sum fun i _ => h1 i
      _ = 2 * ∑ i : Fin n, ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := by rw [Finset.mul_sum]
      _ ≤ 2 * B := by gcongr
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 2 * B ≤ (n₀ : ENNReal) := by
    have h2B : 2 * B ≠ ⊤ := ENNReal.mul_ne_top (by simp) hB
    exact ENNReal.exists_nat_gt h2B |>.imp fun _ h => h.le
  set P : ℕ → Prop := fun n => ∃ Vs : Fin n → Submodule ℂ (Sm E N), (∀ i, D (Vs i)) ∧
    ∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j) with hP
  have hbd : ∀ n, P n → n ≤ n₀ := by
    rintro n ⟨Vs, h1, h2⟩
    exact_mod_cast (key n Vs h1 h2).trans hn₀
  have hP0 : P 0 := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  set n := Nat.findGreatest P n₀ with hn
  obtain ⟨Vs, hVs, hpw⟩ : P n := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  refine ⟨Finset.univ.image Vs, fun V h1 h2 h3 h4 => ?_⟩
  by_contra hno
  have hDV : D V := ⟨h1, h2, h3, h4⟩
  have hno' : ∀ i, ¬ IsoV V (Vs i) := fun i hi => hno ⟨Vs i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩
  have hnext : P (n + 1) := by
    refine ⟨Fin.cons V Vs, fun i => ?_, fun i j hij => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hDV
      · simpa using hVs i
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa using hno' j
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact fun h => hno' i (isoV_symm (hVs i).1.stable h)
        | succ j =>
          simpa using hpw i j fun e => hij (by rw [e])
  have := Nat.le_findGreatest (hbd _ hnext) hnext
  omega

end GlobalTheory.CompanionTheory.FinDiscP

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiTermsSummable
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.Domination

theorem summable_tsum_le_of_shift {ι : Type*} [AddCommGroup ι] {F c : ι → ℝ} (ζ : ι) (hF : ∀ i, 0 ≤ F i)
    (h : ∀ i, F (i + ζ) ≤ c i) (hc : Summable c) : Summable F ∧ ∑' i, F i ≤ ∑' i, c i := by
  have hs : Summable (F ∘ Equiv.addRight ζ) := Summable.of_nonneg_of_le (fun _ => hF _) h hc
  refine ⟨(Equiv.addRight ζ).summable_iff.1 hs, ?_⟩
  rw [← (Equiv.addRight ζ).tsum_eq F]
  exact hs.tsum_le_tsum h hc

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem rt_add_add (η ζ : Matrix (Fin ρ) (Fin p) D.host.E) (y : Mx D ρ p) :
    GlobalTheory.CompanionTheory.FJE.rt (η + ζ) + y = GlobalTheory.CompanionTheory.FJE.rt η + (GlobalTheory.CompanionTheory.FJE.rt ζ + y) := by
  have : GlobalTheory.CompanionTheory.FJE.rt (η + ζ) = GlobalTheory.CompanionTheory.FJE.rt η + GlobalTheory.CompanionTheory.FJE.rt ζ := by
    ext i j
    exact map_add (incA D) _ _
  rw [this, add_assoc]

theorem norm_Wz_shift (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ) (hf : IsLaw χ s f) (g : G D n) (e : G D p)
    (η ζ₂ : Matrix (Fin ρ) (Fin p) D.host.E) (y' x₀ y₀ : Mx D ρ p) (z' : hermA D ρ)
    (hz : M.emb e * (M.nzx 0 x₀ * M.sh y₀) = M.nzx z' (GlobalTheory.CompanionTheory.FJE.rt ζ₂) * M.sh y' * M.emb e) :
    ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y') * M.emb e * g)‖ =
      ‖Wz M m ψ b₀ f (M.sh (η.map (incA D)) * M.emb e * (M.nzx 0 x₀ * (M.sh y₀ * g)))‖ := by
  have e1 : M.sh (η.map (incA D)) * M.emb e * (M.nzx 0 x₀ * (M.sh y₀ * g)) =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * (M.nzx z' (GlobalTheory.CompanionTheory.FJE.rt ζ₂) * (M.sh y' * M.emb e * g)) := by
    calc _ = M.sh (η.map (incA D)) * (M.emb e * (M.nzx 0 x₀ * M.sh y₀)) * g := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hz]
          simp only [mul_assoc]
  have e2 : M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y') * M.emb e * g =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * (M.sh y' * M.emb e * g) := by
    rw [← GlobalTheory.CompanionTheory.FJE.sh_add]
    simp only [mul_assoc]
  have hv : ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ζ₂) (GlobalTheory.CompanionTheory.FJE.rt η)‖ = 1 := hψ.2.1 _
  rw [e1, e2, _root_.GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx M m ψ hψ b₀ χ s f hf, norm_mul, norm_mul,
    (GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀).2.1, hv, one_mul, one_mul]

theorem apply_add_symm {A : Type*} [TopologicalSpace A] [AddCommGroup A] (T : (A × A) ≃ₜ+ (A × A)) {a₁ a₂ b₁ b₂ y : A}
    (h : T (a₁, a₂) = (b₁, b₂)) : T (a₁ + (T.symm (y, 0)).1, a₂ + (T.symm (y, 0)).2) = (b₁ + y, b₂) := by
  have e : (a₁ + (T.symm (y, 0)).1, a₂ + (T.symm (y, 0)).2) = (a₁, a₂) + T.symm (y, 0) := rfl
  rw [e, map_add (f := _), h, T.apply_symm_apply]
  simp


set_option maxHeartbeats 1000000 in
theorem domination : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ)
    (f : G D n → ℂ), IsLaw χ s f → ∀ g : G D n,
    (∀ C : Set (G D n), IsCompact C →
      ∃ c : GlobalTheory.Eis.Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → ℝ, Summable c ∧
        ∀ g ∈ C, ∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ c u) →
    ∃ t : GlobalTheory.Eis.Cosets (P D p) (GF D p) → ℝ, Summable t ∧
      ∀ (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (y : Mx D ρ p),
        Summable (fun η : Matrix (Fin ρ) (Fin p) D.host.E =>
          ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖) ∧
        ∑' η : Matrix (Fin ρ) (Fin p) D.host.E,
          ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖ ≤ t q := by
  intro D n ρ p hn M m ψ hψ b₀ χ s f hf g hdom
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D ρ p
  have hΦ : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 * (M.sh v.1 * g) := by
    have h1 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 :=
      M.nzx_cont.comp (continuous_const.prodMk continuous_snd)
    have h2 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.sh v.1 := M.sh_cont.comp continuous_fst
    exact h1.mul (h2.mul continuous_const)
  obtain ⟨c, hc, hb⟩ := hdom _ ((hK.prod hK).image hΦ)
  refine ⟨fun q => ∑' η, c (q, η), hc.prod, fun q y => ?_⟩
  obtain ⟨T, hT1, -, hT3⟩ := GlobalTheory.T.lattice_translation_preserved M ((q.out : GF D p) : G D p) (q.out : GF D p).2
  obtain ⟨a₁, ha₁, hy⟩ := hKc (T.symm (y, 0)).1
  obtain ⟨a₂, ha₂, hx⟩ := hKc (T.symm (y, 0)).2
  obtain ⟨ξ₁, rfl⟩ : ∃ ξ, GlobalTheory.CompanionTheory.FJE.rt ξ = a₁ := ha₁
  obtain ⟨ξ₂, rfl⟩ : ∃ ξ, GlobalTheory.CompanionTheory.FJE.rt ξ = a₂ := ha₂
  obtain ⟨ζ₁, ζ₂, hζ⟩ := hT1 ξ₁ ξ₂
  have hTv := apply_add_symm (y := y) T hζ
  obtain ⟨z', hz'⟩ := hT3 (GlobalTheory.CompanionTheory.FJE.rt ξ₁ + (T.symm (y, 0)).1) (GlobalTheory.CompanionTheory.FJE.rt ξ₂ + (T.symm (y, 0)).2)
  rw [hTv] at hz'
  refine summable_tsum_le_of_shift ζ₁ (fun _ => norm_nonneg _) (fun η => ?_) (hc.prod_factor q)
  rw [rt_add_add, norm_Wz_shift M m ψ hψ b₀ χ s f hf g _ η ζ₂ _ _ _ z' hz']
  exact hb _ ⟨(_, _), ⟨hy, hx⟩, rfl⟩ (q, η)

end GlobalTheory.CompanionTheory.FJE.Domination
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerOfFibIntEqZero
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem mem_twKer_of_sum {G X ι : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (N : Subgroup G) (T : Finset ι) (hT : T.Nonempty) (g : ι → N) (x : X) (hs : ∑ t ∈ T, ρ (g t : G) x = 0) :
    x ∈ twKer ρ N 1 := by
  have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_pos.ne'
  have hmem : ∀ t ∈ T, x - ρ (g t : G) x ∈ twKer ρ N 1 := by
    intro t _
    have hg : ρ (g t : G) x - (((1 : N →* ℂˣ) (g t) : ℂˣ) : ℂ) • x ∈ twKer ρ N 1 :=
      Submodule.subset_span ⟨g t, x, rfl⟩
    have := (twKer ρ N 1).neg_mem hg
    simpa using this
  have hs' : (T.card : ℂ) • x = ∑ t ∈ T, (x - ρ (g t : G) x) := by
    rw [Finset.sum_sub_distrib, hs, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have h1 : (T.card : ℂ) • x ∈ twKer ρ N 1 := by
    rw [hs']
    exact Submodule.sum_mem _ hmem
  exact ((twKer ρ N 1).smul_mem_iff hc).1 h1

theorem exists_reps {L : Type} [Group L] (K : Subgroup L) (hK : K.FiniteIndex) :
    ∃ T : Finset L, T.Nonempty ∧ ∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K := by
  classical
  haveI : Fintype (L ⧸ K) := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset (L ⧸ K)).image Quotient.out, ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk 1))⟩, ?_⟩
  intro x
  refine ⟨(QuotientGroup.mk x : L ⧸ K).out, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
  · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  · rintro t ⟨ht, hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    have : q = (QuotientGroup.mk x : L ⧸ K) := by
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hx
    rw [this]

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_mulH {n : ℕ} (κ : GL (Fin n) k) : Continuous (mulH κ) := by
  have : Continuous fun y : Fin n → k => (κ : Matrix (Fin n) (Fin n) k).mulVec y :=
    Continuous.matrix_mulVec continuous_const continuous_id
  exact continuous_ofAdd.comp (this.comp continuous_toAdd)

theorem continuous_uMh (n : ℕ) : Continuous (uMh k n) :=
  (_root_.GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj k n).2.1.comp continuous_toAdd

theorem exists_sum_eq_zero_abs (n : ℕ) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) Y) (hρ : IsSmooth ρ)
    (ρ' : Representation ℂ (Multiplicative (Fin n → k)) X) (hρ' : IsSmooth ρ')
    (S : Set (GL (Fin n) k)) (hS : ∀ κ ∈ S, κ ∈ GlobalTheory.SplitWeil.KO k (Fin n))
    (F : GL (Fin n) k → X →ₗ[ℂ] Y)
    (hF : ∀ κ ∈ S, ∀ y x, F κ (ρ' y x) = ρ (mulH κ y) (F κ x))
    (hinj : ∀ x, (∀ κ ∈ S, F κ x = 0) → x = 0)
    (x : X) (hx : ∀ κ ∈ S, F κ x ∈ twKer ρ ⊤ 1) (hfin : ((fun κ => F κ x) '' S).Finite) :
    ∃ T : Finset (Multiplicative (Fin n → k)), T.Nonempty ∧ ∑ y ∈ T, ρ' y x = 0 := by
  classical
  obtain ⟨c, hc, hS'⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer k n ρ _ hfin (by
    rintro _ ⟨κ, hκ, rfl⟩
    exact hx κ hκ)
  have hcomp : IsCompact (Lc n c : Set (Multiplicative (Fin n → k))) := isCompact_Lc n hc
  have hθ : IsOpen (((1 : Lc n c →* ℂˣ).ker : Subgroup (Lc n c)) : Set (Lc n c)) := by
    have : (((1 : Lc n c →* ℂˣ).ker : Subgroup (Lc n c)) : Set (Lc n c)) = Set.univ := by
      ext l
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isOpen_univ
  set K := GlobalTheory.CompanionTheory.TwistedAverage.stabKer ρ' (Lc n c) 1 x with hK
  have hKo : IsOpen (K : Set (Lc n c)) := GlobalTheory.CompanionTheory.TwistedAverage.isOpen_stabKer hρ' _ _ hθ x
  have hKf : K.FiniteIndex := GlobalTheory.CompanionTheory.TwistedAverage.finiteIndex_stabKer hρ' hcomp _ hθ x
  obtain ⟨T, hTn, hT⟩ := exists_reps K hKf
  refine ⟨T.image Subtype.val, hTn.image _, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  refine hinj _ fun κ hκ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hsmooth : IsSmooth (MonoidHom.comp ρ (mulH κ)) := fun v =>
    (hρ v).preimage (continuous_mulH κ)
  have key := _root_.GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer (MonoidHom.comp ρ (mulH κ)) hsmooth (Lc n c) hcomp (F κ x)
    (_root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist k n ρ c κ (hS κ hκ) _ (hS' _ ⟨κ, hκ, rfl⟩)) K T hKo
    (fun l hl => by
      have h1 : ρ' (l : Multiplicative (Fin n → k)) x = x := hl.1
      have h2 := hF κ hκ (l : Multiplicative (Fin n → k)) x
      rw [h1] at h2
      exact h2.symm) hT
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  exact hF κ hκ _ x

theorem mem_twKer_fibAct (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    (φ : fibM (Fin t → k) Z) (h : smInt μ φ.1 ∈ twKer ρ₀ ⊤ 1) : φ ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  classical
  obtain ⟨c, hc, hinv⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant k t φ.1 φ.2.1 φ.2.2
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators k t φ.1 c hc φ.2.2 hinv
  have hφ : φ.1 = fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ.1 a) v := funext hA
  have hsum : φ = ∑ a ∈ A, cosetFn t hc a (φ.1 a) := by
    apply Subtype.ext
    funext v
    rw [hA v, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hI := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum.smInt_sum_coset k t μ c hc A φ.1
  rw [← hφ] at hI
  rw [hI] at h
  have hz : ∑ a ∈ A, φ.1 a ∈ twKer ρ₀ ⊤ 1 := ((twKer ρ₀ ⊤ 1).smul_mem_iff (_root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero k t μ c hc)).1 h
  have h0 : cosetFn t hc 0 (∑ a ∈ A, φ.1 a) = ∑ a ∈ A, cosetFn t hc 0 (φ.1 a) := by
    apply Subtype.ext
    funext v
    rw [Submodule.coe_sum, Finset.sum_apply]
    have e : ∀ z : Z, (cosetFn t hc 0 z).1 v = (cosetSet t c 0).indicator (fun _ => z) v := fun _ => rfl
    simp only [e]
    by_cases hv : v ∈ cosetSet t c 0
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv, Finset.sum_const_zero]
  have hd : φ - cosetFn t hc 0 (∑ a ∈ A, φ.1 a) ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
    have e : φ - cosetFn t hc 0 (∑ a ∈ A, φ.1 a) = ∑ a ∈ A, (cosetFn t hc a (φ.1 a) - cosetFn t hc 0 (φ.1 a)) := by
      rw [h0, Finset.sum_sub_distrib, ← hsum]
    rw [e]
    exact Submodule.sum_mem _ fun a _ => _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer k i t ρ₀ c hc a _
  have := (twKer (fibAct t ρ₀) ⊤ 1).add_mem hd (GlobalTheory.T.coset_function_jacquet_kernel k i t ρ₀ c hc _ hz)
  simpa using this

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    (κ : GL (Fin (i + t)) k) : cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] fibM (Fin t → k) (V ⊗[ℂ] W) :=
  LinearMap.codRestrict (fibM (Fin t → k) (V ⊗[ℂ] W))
    (LinearMap.pi fun v => evL (τ := τ) (σ := σ) (uM k (i + t) (midV k i t v) * levi k (i + t) κ))
    (fun x => _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main k i t τ σ hτ hσ x κ)

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_of_fibInt_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ f : cIndSpace (HPG k i t) (hRep τ σ), (∀ g, fibInt μ f g = 0) → f ∈ twKer (prodPG τ σ) (MirUin k (i + t)) 1 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f hf
  classical
  have hsm₀ : IsSmooth (topRep τ W) := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep k i τ hτ
  have hsm : IsSmooth (fibAct t (topRep τ W)) := GlobalTheory.T.smooth_fibre_action k i t (topRep τ W) hsm₀
  have hsmP : IsSmooth (MonoidHom.comp (prodPG τ σ) (uMh k (i + t))) := fun v =>
    (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd _ _ v).preimage (continuous_uMh (i + t))
  have hker : ∀ κ, fibLin τ σ hτ hσ κ f ∈ twKer (fibAct t (topRep τ W)) ⊤ 1 := fun κ =>
    mem_twKer_fibAct i t (topRep τ W) μ (fibLin τ σ hτ hσ κ f) (_root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero k i τ _ (hf κ))
  have hfin : ((fun κ => fibLin τ σ hτ hσ κ f) '' (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
    refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    rw [Set.image_image]
    exact _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_fibV_image k i t τ σ f
  have hF : ∀ κ ∈ (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k)), ∀ y x,
      fibLin τ σ hτ hσ κ (MonoidHom.comp (prodPG τ σ) (uMh k (i + t)) y x) =
        fibAct t (topRep τ W) (mulH κ y) (fibLin τ σ hτ hσ κ x) := by
    intro κ _ y x
    apply Subtype.ext
    funext v
    exact _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU.fibV_uM k i t τ σ x y.toAdd κ v
  have hinj : ∀ x, (∀ κ ∈ (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k)), fibLin τ σ hτ hσ κ x = 0) → x = 0 := by
    intro x hx
    exact _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero k i t τ σ x fun κ hκ => congrArg Subtype.val (hx κ hκ)
  obtain ⟨T, hTn, hT⟩ := exists_sum_eq_zero_abs (i + t) (fibAct t (topRep τ W)) hsm
    (MonoidHom.comp (prodPG τ σ) (uMh k (i + t))) hsmP _ (fun _ h => h) (fibLin τ σ hτ hσ) hF hinj f
    (fun κ _ => hker κ) hfin
  exact mem_twKer_of_sum (prodPG τ σ) (MirUin k (i + t)) T hTn
    (fun y => ⟨uM k (i + t) y.toAdd, uM_mem k (i + t) y.toAdd⟩) f hT

end
end

