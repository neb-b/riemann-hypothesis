module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0721
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0719
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0649
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0612
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0720
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0717
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0645
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummable

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNode
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.NodeCarry

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s : ℕ}

theorem mul_mem_Sm {e φ : GA E N → ℂ} (he : e ∈ Sm E N) (hφ : φ ∈ Sm E N) :
    (fun x => e x * φ x) ∈ Sm E N := by
  intro g
  refine ((he g).mul (hφ g)).congr fun x hx => ?_
  have hx' : IsUnit (Matrix.of x) := hx
  simp [chart, hx']

theorem memInd2_of_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 g + y.1 g
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => Submodule.smul_mem _ c (hx.2 k g)⟩
    change c • x.1 _ = c • x.1 g
    rw [hx.1]

theorem carries_translate {e : GA E N → ℂ} {U U' : Submodule ℂ (Sm E N)} (hU : FinStable U) (hU' : FinStable U')
    (hc : Carries e U U') (P : GL (Fin N) (Af E)) {a : Sm E N} (ha : a ∈ U) :
    ∃ a' ∈ U', ∀ m, a'.1 m = e (m * finGL E N P) * a.1 m := by
  obtain ⟨b, hb, hbe⟩ := hc _ (hU P⁻¹ a ha)
  refine ⟨act (.fin P) b, hU' P b hb, fun m => ?_⟩
  have e1 : (act (.fin P) b).1 m = b.1 (m * finGL E N P) := rfl
  have e2 : (act (.fin P⁻¹) a).1 (m * finGL E N P) = a.1 (m * finGL E N P * finGL E N P⁻¹) := rfl
  rw [e1, hbe, e2, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem finGL_unip (x : BlockIx (r + s) r → Af E) : finGL E (r + s) (unip x) = unip fun p => sFin E (x p) := by
  refine ga_ext ?_ ?_
  · rw [pInf_finGL, IwaAd.map_unip]
    have : (fun p => pInf E (sFin E (x p))) = 0 := funext fun p => map_zero (infEq E).symm
    rw [this]
    exact unip_zero.symm
  · rw [pFin_finGL, IwaAd.map_unip]
    rfl

theorem finGL_lev (p : GL (Fin r) (Af E) × GL (Fin s) (Af E)) :
    finGL E (r + s) (lev (Af E) r s p) = lev (Ad E) r s (finGL E r p.1, finGL E s p.2) := by
  refine ga_ext ?_ ?_
  · rw [pInf_finGL, IwaAd.map_lev, pInf_finGL, pInf_finGL]
    exact (map_one (lev (Cinf E) r s)).symm
  · rw [pFin_finGL, IwaAd.map_lev, pFin_finGL, pFin_finGL]

theorem nodeFn_slice {e₁ : GA E r → ℂ} {e₂ : GA E s → ℂ} (h₁ : FlatFn e₁) (h₂ : FlatFn e₂) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)) : ∃ p : GL (Fin r) (Af E) × GL (Fin s) (Af E), ∀ m : GA E r × GA E s,
      nodeFn e₁ e₂ (lev (Ad E) r s m * cf (r + s) k g) = e₁ (m.1 * finGL E r p.1) * e₂ (m.2 * finGL E s p.2) := by
  obtain ⟨xf, p, c, hc, hg⟩ := IwaFin.exists_unip_lev_integral E r s g
  refine ⟨p, fun m => ?_⟩
  obtain ⟨v, hv⟩ := lev_mul_unip m fun q => sFin E (xf q)
  have e1 : cf (r + s) k g = unip (fun q => sFin E (xf q)) * lev (Ad E) r s (finGL E r p.1, finGL E s p.2) *
      cf (r + s) k c := by
    rw [hg, cf, cf, map_mul _ (unip xf * _) c, ← mul_assoc, infGL_comm, mul_assoc (finGL _ _ _), map_mul, finGL_unip,
      finGL_lev]
  rw [e1, ← mul_assoc, ← mul_assoc, hv, mul_assoc (unip v), ← map_mul]
  exact _root_.GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply e₁ e₂ h₁ h₂ v _ k c hc

theorem carries_nodeFn : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (U₁ U₁' : Submodule ℂ (Sm E r)) (U₂ U₂' : Submodule ℂ (Sm E s)), FlatFn e₁ → FlatFn e₂ → FinStable U₁ → FinStable U₁' → FinStable U₂ → FinStable U₂' → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → Carries (nodeFn e₁ e₂) (indSpan U₁ U₂) (indSpan U₁' U₂') := by
  intro E _ _ _ r s e₁ e₂ U₁ U₁' U₂ U₂' h₁ h₂ s₁ s₁' s₂ s₂' c₁ c₂ φ hφ
  have hF := _root_.GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn e₁ e₂ h₁ h₂
  have hI := memInd2_of_mem hφ
  refine ⟨⟨fun x => nodeFn e₁ e₂ x * φ.1 x, mul_mem_Sm hF.sm φ.2⟩,
    Submodule.subset_span ⟨fun u g => ?_, fun k g => ?_⟩, fun _ => rfl⟩
  · change nodeFn e₁ e₂ (unip u * g) * φ.1 (unip u * g) = nodeFn e₁ e₂ g * φ.1 g
    rw [hI.1]
    obtain ⟨v, m, k, c, hc, rfl⟩ := exists_iw g
    rw [← mul_assoc, ← mul_assoc, ← D.unip_add', _root_.GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply e₁ e₂ h₁ h₂ _ _ _ _ hc,
      _root_.GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply e₁ e₂ h₁ h₂ _ _ _ _ hc]
  · obtain ⟨p, hp⟩ := nodeFn_slice h₁ h₂ k g
    obtain ⟨n, ψ₁, ψ₂, u₁, u₂, hs⟩ := tensor_pair_finite_sum (hI.2 k g)
    choose a ha hae using fun i => carries_translate s₁ s₁' c₁ p.1 (u₁ i)
    choose b hb hbe using fun i => carries_translate s₂ s₂' c₂ p.2 (u₂ i)
    convert A.sum_mem ha hb using 1
    funext m
    have hm : φ.1 (lev (Ad E) r s m * cf (r + s) k g) = ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := congrFun hs m
    change nodeFn e₁ e₂ (lev (Ad E) r s m * cf (r + s) k g) * φ.1 (lev (Ad E) r s m * cf (r + s) k g) = _
    rw [hm, hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hae, hbe]
    ring

end GlobalTheory.CompanionTheory.LimV.NodeCarry
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientHeisenbergEquivariance
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem Wz_sh_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ)
    (f : G D n → ℂ), IsLaw χ s f → ∀ (η : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p) (h : G D n),
    Wz M m ψ b₀ f (M.sh η * (M.nzx z x * h)) =
      chz ψ b₀ z * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x η * Wz M m ψ b₀ f (M.sh η * h) := by
  intro D n ρ p hn M m ψ hψ b₀ χ s f hf η z x h
  obtain ⟨hadd, hnorm, -, -⟩ := _root_.GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀
  have hjc := _root_.GlobalTheory.CompanionTheory.FJE.chz_jc ψ b₀ η x
  have hsh := _root_.GlobalTheory.CompanionTheory.FJE.sh_mul_nzx M η z x
  have hmul := _root_.GlobalTheory.CompanionTheory.NzxAdd.nzx_add M
  have hw := _root_.GlobalTheory.CompanionTheory.FJE.LawW.law_w M χ s f hf
  have e1 : M.sh η * (M.nzx z x * h) = M.nzx (z + jc η x) x * (M.sh η * h) := by
    rw [← mul_assoc, hsh, mul_assoc]
  rw [e1]
  generalize M.sh η * h = h'
  have hc : chz ψ b₀ z * chv ψ b₀ x η = chz ψ b₀ (z + jc η x) := by rw [hadd, hjc]
  rw [hc]
  generalize z + jc η x = c
  have hcc : chz ψ b₀ c * conj (chz ψ b₀ c) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  have hconj : ∀ t, conj (chz ψ b₀ t) = conj (chz ψ b₀ (t + c)) * chz ψ b₀ c := by
    intro t
    have hh : conj (chz ψ b₀ (t + c)) * chz ψ b₀ c = conj (chz ψ b₀ t) * (chz ψ b₀ c * conj (chz ψ b₀ c)) := by
      rw [hadd, map_mul]; ring
    rw [hh, hcc, mul_one]
  have hpt : ∀ t : hermA D ρ, f (M.w * M.nzx t 0 * (M.nzx c x * h')) =
      f (M.w * M.nzx (t + c) 0 * h') := by
    intro t
    have e2 : M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by
      have a1 : M.nzx t 0 * M.nzx c x = M.nzx 0 x * M.nzx (t + c) 0 := by
        rw [hmul, hmul]; simp
      calc M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * (M.nzx t 0 * M.nzx c x) * h' := by
            simp only [mul_assoc]
        _ = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by
            rw [a1]; simp only [mul_assoc]
    rw [e2, hw, mul_assoc]
  haveI := m.hz.1
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  unfold Wz
  calc ∫ t, f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) ∂m.lz
      = ∫ t, (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) (t + c) ∂m.lz := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) = f (M.w * M.nzx (t + c) 0 * h') * (conj (chz ψ b₀ (t + c)) * chz ψ b₀ c)
        rw [hpt, ← hconj]
    _ = ∫ u, f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c) ∂m.lz :=
        integral_add_right_eq_self (μ := m.lz)
          (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) c
    _ = chz ψ b₀ c * ∫ u, f (M.w * M.nzx u 0 * h') * conj (chz ψ b₀ u) ∂m.lz := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show _ = _
        ring

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisCells
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCellsChapter

theorem eisCells : PositivityTheory.GramSchwartzFunctions.EisCells :=
  _root_.GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of _root_.GlobalTheory.CompanionTheory.BruhatCell.bruhat _root_.GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn _root_.GlobalTheory.CompanionTheory.EisCellsPInv.pInv
    (_root_.GlobalTheory.CompanionTheory.EisCells.term_of_covariance _root_.GlobalTheory.CompanionTheory.HeisSchwartz.heisSch_holds _root_.GlobalTheory.CompanionTheory.EisCovar.covar GlobalTheory.T.eisenstein_vanishing _root_.GlobalTheory.CompanionTheory.EisUnfold.unfold2 _root_.GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv)

end GlobalTheory.CompanionTheory.EisCellsChapter
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesLeviStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_intertwines_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (u : Mir k (i + t)), u ∈ MirUin k (i + t) → ∀ g : GL (Fin (i + t)) k, fibInt μ (prodPG τ σ u f) g = fibInt μ f g := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip | exact GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralSupportSubgroup
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

theorem smInt_zero_fun {X Z : Type} [MeasurableSpace X] [AddCommGroup Z] [Module ℂ Z]
    (μ : MeasureTheory.Measure X) (φ : X → Z) (h : ∀ x, φ x = 0) : smInt μ φ = 0 := by
  unfold smInt
  apply finsum_eq_zero_of_forall_eq_zero
  intro v
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have hempty : φ ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hv (hx.symm.trans (h x))
    rw [hempty]
    simp

theorem mem_of_eq_mul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k))
    (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (h : HPG k i t) (β : Mir k (i + t)) (hβ : β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK)
    (e : uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β) :
    ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b' := by
  obtain ⟨y', _, b', hb', hβe⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_Bgrp.1 hβ
  obtain ⟨x, q, hx⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main k i t h
  have e2 : uM k (i + t) y * levi k (i + t) g =
      uM k (i + t) (topV k i t x + ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y') *
        levi k (i + t) ((q : GL (Fin (i + t)) k) * b') := by
    calc uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β := e
      _ = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) *
            (uM k (i + t) y' * levi k (i + t) b') := by rw [hx, hβe]
      _ = _ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_mul_uM_levi _ _ _ _ _
  exact ⟨q, b', hb', (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_inj _ e2).2⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ c K₁ hK b hb g hg
  have hz : ∀ v, fibV b g v = 0 := by
    intro v
    by_contra hne
    have hex : ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
        uM k (i + t) (midV k i t v) * levi k (i + t) g = (h : Mir k (i + t)) * β := by
      by_contra hno
      exact hne (hb _ hno)
    obtain ⟨h, β, hβ, e⟩ := hex
    exact hg (mem_of_eq_mul k i t c K₁ hK _ g h β hβ e)
  show clT τ W (smInt μ (fibV b g)) = 0
  rw [smInt_zero_fun μ _ hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingOpenSubgroup
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

theorem fibV_mul_right_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ b' ∈ K₁, ∀ g : GL (Fin (i + t)) k, fibV b (g * b') = fibV b g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b hval hzero b' hb' g
  have hβ : GlobalTheory.BZMir.levi k (i + t) b' ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := by
    show ∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c, ∃ a ∈ K₁,
      GlobalTheory.BZMir.levi k (i + t) b' = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) a
    exact ⟨0, zero_mem _, b', hb', by rw [GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, one_mul]⟩
  have key : ∀ p : GlobalTheory.BZMir.Mir k (i + t), ∀ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
      b.1.1.1 (p * β) = b.1.1.1 p := by
    intro p β hβ
    by_cases hp : ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
        ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀
    · obtain ⟨h, β₀, hβ₀, rfl⟩ := hp
      rw [mul_assoc, hval h (β₀ * β) (Subgroup.mul_mem _ hβ₀ hβ), hval h β₀ hβ₀]
    · have hp' : ¬ ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
          ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
            p * β = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀ := by
        rintro ⟨h, β₀, hβ₀, he⟩
        refine hp ⟨h, β₀ * β⁻¹, Subgroup.mul_mem _ hβ₀ (Subgroup.inv_mem _ hβ), ?_⟩
        rw [← mul_assoc, ← he, mul_inv_cancel_right]
      rw [hzero _ hp', hzero _ hp]
  funext v
  unfold GlobalTheory.CompanionTheory.BZPsiPG.fibV
  rw [map_mul, ← mul_assoc]
  exact key _ _ hβ

end GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingSubgroup
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

theorem fibV_one_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → fibV b 1 = (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)).indicator (fun _ => z) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b h1 h2
  funext v
  by_cases hv : v ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c
  · rw [Set.indicator_of_mem (show v ∈ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)) from hv)]
    have hm : midV k i t v ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c := by
      intro j
      induction j using Fin.addCases with
      | left j =>
        show Fin.append (0 : Fin i → k) v (Fin.castAdd t j) ∈ _
        rw [Fin.append_left]
        exact (zero_mem (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt i c)) j
      | right j =>
        show Fin.append (0 : Fin i → k) v (Fin.natAdd i j) ∈ _
        rw [Fin.append_right]
        exact hv j
    have hp : uM k (i + t) (midV k i t v) * levi k (i + t) 1 ∈
        GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := ⟨_, hm, 1, one_mem _, rfl⟩
    have e := h1 1 _ hp
    rw [map_one] at e
    simpa [fibV] using e
  · rw [Set.indicator_of_notMem (show v ∉ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)) from hv)]
    apply h2
    rintro ⟨h, β, hβ, e⟩
    obtain ⟨x, q, hq⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main k i t h
    obtain ⟨y, hy, b', hb', rfl⟩ := hβ
    rw [hq, uM_levi_mul_uM_levi] at e
    obtain ⟨e1, e2⟩ := uM_levi_inj _ (show uM k (i + t) (midV k i t v) * levi k (i + t) 1 = _ from e)
    have hq' : (q : GL (Fin (i + t)) k) = b'⁻¹ := eq_inv_of_mul_eq_one_left e2.symm
    apply hv
    intro j
    have e3 := congrFun e1 (Fin.natAdd i j)
    have e4 : midV k i t v (Fin.natAdd i j) = v j := Fin.append_right _ _ _
    have e5 : topV k i t x (Fin.natAdd i j) = 0 := Fin.append_right _ _ _
    rw [Pi.add_apply, e4, e5, zero_add, hq'] at e3
    rw [e3]
    exact mulVec_mem_latt (hK (inv_mem hb')) hy _

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonHermMain
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

theorem poissonHerm_main : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm := by
  intro D r V ψ θ μ lam ν φ hH hJ
  obtain ⟨hm, hψ, hθ, hμ, ⟨𝓖, hlam⟩, -, hφ, -⟩ := hH
  have hc := _root_.GlobalTheory.CompanionTheory.BigCellJ.jt_continuous D r V ψ θ μ φ hψ hθ hμ hφ
  have hu := _root_.GlobalTheory.CompanionTheory.JtUnif.jt_unif D r V ψ θ μ φ hm hψ hθ hμ hφ
  have hW := _root_.GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank D r V ψ θ μ lam 𝓖 φ hm hψ hθ hμ hlam hφ
  obtain ⟨-, hP⟩ := GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam 𝓖 hlam _ hc hu
  have hgW : ∀ β : HermE D r, (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) ((hermEquiv (D := D) (r := r)) β) = W ψ V μ lam φ β :=
    fun β => (W_eq ψ V μ lam φ β).symm
  have hS : Summable (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
    refine (hermEquiv (D := D) (r := r)).summable_iff.1 ?_
    exact hW.congr fun β => (hgW β).symm
  have e := hP hS
  have hsumJ : ∑' b : HermE D r, J ψ V μ φ b = ∑' c : ratHerm D r, Jt ψ V μ φ c.1 :=
    (hermEquiv (D := D) (r := r)).tsum_eq (fun c => Jt ψ V μ φ c.1)
  have hsumW : ∑' β : HermE D r, W ψ V μ lam φ β = ∑' t : ratHerm D r, ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam := by
    rw [← (hermEquiv (D := D) (r := r)).tsum_eq]
    exact tsum_congr fun β => (hgW β).symm
  rw [hsumJ, e, ← hsumW]
  exact hW.hasSum

end GlobalTheory.CompanionTheory.HermPoisson
end
end

