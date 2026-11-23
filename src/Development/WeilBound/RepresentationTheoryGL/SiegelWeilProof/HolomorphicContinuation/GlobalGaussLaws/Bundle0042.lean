module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0040
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0041
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.QuadraticOperatorPureTensor

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

theorem gens_inv (g : G D n)
    (hg : (∃ b, mat g⁻¹ = blk4 1 b 0 1) ∨ (∃ a d, mat g⁻¹ = blk4 a 0 0 d) ∨ (∃ c, mat g⁻¹ = blk4 1 0 c 1)) :
    (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1) := by
  have hgg : g = (g⁻¹)⁻¹ := (inv_inv g).symm
  rcases hg with ⟨b, hb⟩ | ⟨a, d, h⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨-adj b, ?_⟩
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hb]; simp [adj_one, adj_zero]
  · refine Or.inr (Or.inl ⟨adj d, adj a, ?_⟩)
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ h]; simp [adj_zero]
  · refine Or.inr (Or.inr ⟨-adj c, ?_⟩)
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hc]; simp [adj_one, adj_zero]

theorem closure_triv (hG : GenA) (hDA : DecompAway) {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι) (x : G D n) (hx : IsTrivAt θ τ x) :
    x ∈ Submonoid.closure {x : G D n | IsTrivAt θ τ x ∧
      ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))} := by
  classical
  letI : Inv (Set (G D n)) := Set.inv
  choose π yf hπ using fun g => hDA D n θ τ ι hθ hι g
  have πmul : ∀ g h : G D n, π (g * h) = π g * π h := by
    intro g h
    have e1 := (hπ (g * h)).2.1
    have hg := (hπ g).2.1
    have hh := (hπ h).2.1
    have hc := (hπ h).2.2 (yf g)
    have e2 : g * h = (π g * π h) * ι (yf g * yf h) := by
      calc g * h = π g * ι (yf g) * (π h * ι (yf h)) := by rw [← hg, ← hh]
        _ = π g * (ι (yf g) * π h) * ι (yf h) := by group
        _ = π g * (π h * ι (yf g)) * ι (yf h) := by rw [hc]
        _ = (π g * π h) * ι (yf g * yf h) := by rw [map_mul]; group
    have e3 : π (g * h) * ι (yf (g * h)) = (π g * π h) * ι (yf g * yf h) := e1.symm.trans e2
    have hy := uniq_dec hι (hπ (g * h)).1 (triv_mul (hπ g).1 (hπ h).1) e3
    rw [hy] at e3
    exact mul_right_cancel e3
  have πtriv : ∀ a, IsTrivAt θ τ a → π a = a := by
    intro a ha
    have e1 := (hπ a).2.1
    have hy := uniq_dec hι (hπ a).1 ha (show π a * ι (yf a) = a * ι 1 by rw [← e1, map_one, mul_one])
    rw [hy, map_one, mul_one] at e1
    exact e1.symm
  have fz : ((0 : Mx D n n)).map (finPart D) = 0 := Matrix.map_zero _ (map_zero _)
  have fo : ((1 : Mx D n n)).map (finPart D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have gen : ∀ s : G D n, ((∃ b, mat s = blk4 1 b 0 1) ∨ (∃ a d, mat s = blk4 a 0 0 d) ∨ (∃ c, mat s = blk4 1 0 c 1)) →
      IsTrivAt θ τ (π s) ∧ ((∃ b, mat (π s) = blk4 1 b 0 1) ∨ (∃ a d, mat (π s) = blk4 a 0 0 d) ∨
        (∃ c, mat (π s) = blk4 1 0 c 1)) := by
    intro s hs
    refine ⟨(hπ s).1, ?_⟩
    have e := (hπ s).2.1
    have hps : π s = s * (ι (yf s))⁻¹ := eq_mul_inv_of_mul_eq e.symm
    have hMaway : ∀ τ', τ' ≠ τ → compAt θ τ' (mat (ι (yf s))) = 1 := fun τ' h => (hι.2 (yf s)).2.1 τ' h
    have hMf : (mat (ι (yf s))).map (finPart D) = 1 := (hι.2 (yf s)).2.2
    have hMτ : compAt θ τ (mat (ι (yf s))) = compAt θ τ (mat s) := by
      have : compAt θ τ (mat s) = compAt θ τ (mat (π s)) * compAt θ τ (mat (ι (yf s))) := by
        conv_lhs => rw [e]
        rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul']
      rw [this, (hπ s).1, Matrix.one_mul]
    have hmat : mat (π s) = mat s * mat (ι (yf s))⁻¹ := by rw [hps, GlobalTheory.StdUnn.LeftInvSect.mat_mul]
    rcases hs with ⟨b, hb⟩ | ⟨a, d, had⟩ | ⟨c, hc⟩
    · rw [hb, component_block_matrix, compAt_one', compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, hA, -, hC, hE, haw, hAf, -, hCf, hEf⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hA1 : A = 1 := eq_of_comps hθ (by rw [hA, compAt_one']) (fun τ' h => by rw [(haw τ' h).1, compAt_one'])
        (by rw [hAf, fo])
      have hC0 : C = 0 := eq_of_comps hθ (by rw [hC, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.2.1, compAt_zero'])
        (by rw [hCf, fz])
      have hE1 : E' = 1 := eq_of_comps hθ (by rw [hE, compAt_one']) (fun τ' h => by rw [(haw τ' h).2.2.2, compAt_one'])
        (by rw [hEf, fo])
      rw [hA1, hC0, hE1] at hM
      refine Or.inl ⟨-adj B + b, ?_⟩
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, hb, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_one, adj_zero]
    · rw [had, component_block_matrix, compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, -, hB, hC, -, haw, -, hBf, hCf, -⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hB0 : B = 0 := eq_of_comps hθ (by rw [hB, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.1, compAt_zero'])
        (by rw [hBf, fz])
      have hC0 : C = 0 := eq_of_comps hθ (by rw [hC, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.2.1, compAt_zero'])
        (by rw [hCf, fz])
      rw [hB0, hC0] at hM
      refine Or.inr (Or.inl ⟨a * adj E', d * adj A, ?_⟩)
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, had, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_zero]
    · rw [hc, component_block_matrix, compAt_one', compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, hA, hB, -, hE, haw, hAf, hBf, -, hEf⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hA1 : A = 1 := eq_of_comps hθ (by rw [hA, compAt_one']) (fun τ' h => by rw [(haw τ' h).1, compAt_one'])
        (by rw [hAf, fo])
      have hB0 : B = 0 := eq_of_comps hθ (by rw [hB, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.1, compAt_zero'])
        (by rw [hBf, fz])
      have hE1 : E' = 1 := eq_of_comps hθ (by rw [hE, compAt_one']) (fun τ' h => by rw [(haw τ' h).2.2.2, compAt_one'])
        (by rw [hEf, fo])
      rw [hA1, hB0, hE1] at hM
      refine Or.inr (Or.inr ⟨c + -adj C, ?_⟩)
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, hc, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_one, adj_zero]
  set S : Set (G D n) := {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}
    with hSdef
  have hxS : x ∈ Submonoid.closure (S ∪ S⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, hG D n]
    show x ∈ (⊤ : Subgroup (G D n))
    exact Subgroup.mem_top x
  have key : ∀ g ∈ Submonoid.closure (S ∪ S⁻¹), π g ∈ Submonoid.closure {x : G D n | IsTrivAt θ τ x ∧
      ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))} := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      apply Submonoid.subset_closure
      rcases hg with hg | hg
      · exact gen g hg
      · exact gen g (gens_inv g hg)
    | one => rw [πtriv 1 triv_one]; exact one_mem _
    | mul g h _ _ ihg ihh => rw [πmul]; exact mul_mem ihg ihh
  have := key x hxS
  rwa [πtriv x hx] at this

end PositivityTheory.Rg.Sw.Glob.AW
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def OpCLM : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ∃ L : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ),
        (ω (ι y) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩).1 = tens θ τ fr (L S) Ψ

def AwayFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), g = x * ι y ∧ ∀ Ψ, AwayCls θ τ fr Ψ → ∃ Ψ', AwayCls θ τ fr Ψ' ∧
      ∀ (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ) (hS : tens θ τ fr S Ψ ∈ schwartzA θ V.rank n),
        (ω x ⟨tens θ τ fr S Ψ, hS⟩).1 = tens θ τ fr S Ψ'

def SchDeriv : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n),
    ∃ (S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ) (S' : SchwartzMap (Fin m → Fin n → ℂ) ℂ),
      (∀ t y, S t y = fP c P ((NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin m) (Fin m) ℂ) * (Matrix.of y : Matrix (Fin m) (Fin n) ℂ))) ∧
      (∀ y, S' y = fP c (vfX c X P) y) ∧
        Filter.Tendsto (fun t : ℝ => t⁻¹ • (S t - S 0)) (nhdsWithin 0 {0}ᶜ) (nhds S')

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IntegrableRho
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def rr (m n : ℕ) : ℝ := ((Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 : ℕ) : ℝ)

theorem integrable_rho : Integrable (fun u : Fin m → Fin n → ℂ => (1 + ‖u‖) ^ (-rr m n)) := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  apply integrable_one_add_norm
  unfold rr; push_cast; linarith


set_option synthInstance.maxHeartbeats 400000 in
theorem hloc_away {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (K : Set (Fin m → Fin n → ℂ)) (hK : IsCompact K) :
    ∫⁻ z, K.indicator 1 (piF θ τ fr z) * ‖Ψ z‖ₑ ∂μ ≠ ∞ := by
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) 1 one_pos
  have hmem := hΨ.2 (gs 1) ⟨S, funext hS⟩
  have hI := GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ μ ⟨_, hmem⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hgc : Continuous fun u : Fin m → Fin n → ℂ => ‖gs (n := n) 1 u‖ :=
    continuous_norm.comp (S.continuous.congr fun u => hS u)
  obtain ⟨u0, -, hu0⟩ := hK.exists_isMinOn hne hgc.continuousOn
  have hδ : 0 < ‖gs (n := n) 1 u0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hle : ∀ z, K.indicator 1 (piF θ τ fr z) * ‖Ψ z‖ₑ ≤
      ENNReal.ofReal (‖gs (n := n) 1 u0‖)⁻¹ * ‖tens θ τ fr (gs 1) Ψ z‖ₑ := by
    intro z
    by_cases hz : piF θ τ fr z ∈ K
    · rw [Set.indicator_of_mem hz, Pi.one_apply, one_mul]
      have h1 : tens θ τ fr (gs 1) Ψ z = gs (n := n) 1 (piF θ τ fr z) * Ψ z := rfl
      rw [h1, enorm_mul, ← mul_assoc]
      conv_lhs => rw [← one_mul ‖Ψ z‖ₑ]
      gcongr
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← div_eq_inv_mul, one_le_div hδ]
      exact hu0 hz
    · rw [Set.indicator_of_notMem hz, zero_mul]; exact zero_le
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.hasFiniteIntegral.ne


set_option synthInstance.maxHeartbeats 800000 in
theorem hint_int {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Integrable (fun z => (1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n) * ‖Bw ψ V θ τ fr Ψ x z‖) μ := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hΨc := cont_of_away hθ hΨ
  have hπ := continuous_piF (n := n) hθ τ fr
  obtain ⟨c, hc⟩ := Fib.fib_meas μ (piF θ τ fr) hπ (sIns τ fr) (piF_sIns hθ τ hdet) (fun z => ‖Ψ z‖ₑ)
    hΨc.enorm.measurable (fun z u => by simp only [away_add hθ hΨ]) (hloc_away hθ μ hΨ)
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  refine ⟨((hρc.comp hπ).mul (continuous_Bw hθ hψ hΨ x).norm).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e1 : ∀ z, ‖(1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n) * ‖Bw ψ V θ τ fr Ψ x z‖‖ₑ =
      ENNReal.ofReal ((1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n)) * ‖Ψ z‖ₑ := by
    intro z
    rw [enorm_mul, norm_Bw hψ, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (Ψ z), Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      enorm_norm, ofReal_norm_eq_enorm]
  simp_rw [e1]
  have e2 : ∫⁻ z, ENNReal.ofReal ((1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n)) * ‖Ψ z‖ₑ ∂μ =
      ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖) ^ (-rr V.rank n)) ∂((μ.withDensity fun z => ‖Ψ z‖ₑ).map (piF θ τ fr)) := by
    rw [lintegral_map (f := fun u : Fin V.rank → Fin n → ℂ => ENNReal.ofReal ((1 + ‖u‖) ^ (-rr V.rank n)))
      (ENNReal.measurable_ofReal.comp hρc.measurable) hπ.measurable]
    have e := lintegral_withDensity_eq_lintegral_mul μ hΨc.enorm.measurable
      ((ENNReal.measurable_ofReal.comp hρc.measurable).comp hπ.measurable)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  rw [e2, hc, lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have hI := (integrable_rho (m := V.rank) (n := n)).hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) hI
  congr 1; ext u
  rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacB
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem const_of_annS {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (h : ∀ X, annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) = 0) :
    Q = C (evX Q 0) := by
  have hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0 := by
    intro u W
    have e := congrFun (h (fr * W)) (xL θ τ (fr * u))
    rw [annS_tens hθ hfr hM l] at e
    have hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v := fun v => by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
    have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
      have := congrFun (compAt_xL hθ τ (fr * u)) τ
      simpa [dirAt_self] using this
    have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
      unfold psi0
      rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
      simp only [one_mul]
      exact gaussian_at_zero_eq_one D V.rank n
    rw [hc, hinv, hinv, hp, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)
  have hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0 := by
    intro u
    let F : ℝ → ℂ := fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q
    have hF : ∀ t, HasDerivAt F 0 t := by
      intro t
      have hd := GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t
      refine hd.congr_deriv ?_
      have e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u) :=
        (ptX_add_smul _ _ t).symm
      rw [e2]
      exact hk _ u
    have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0
    have e1 : F 1 = evX Q u := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q
      rw [Complex.ofReal_one, one_smul]
      have e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u := by
        funext k
        obtain ⟨a, i, b⟩ := k
        cases b <;> simp [ptX]
      rw [e3]
    have e0 : F 0 = evX Q 0 := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    rw [← e1, ← e0, hc]
  apply sub_eq_zero.1
  apply evX_eq_zero
  intro u
  show eval _ (Q - C (evX Q 0)) = 0
  rw [map_sub, eval_C]
  exact sub_eq_zero.2 (hconst u)

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem mat_mOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (A : GL (Fin n) ℂ) :
    mat (ι (mOf A)) = blk4 (unitAt hσ τ A).1 0 0 (adj ((unitAt hσ τ A)⁻¹).1) := by
  have hU : ((unitAt hσ τ A).1).map (finPart D) = 1 := by
    rw [unitAt_val]
    exact finite_part_adelic_point_matrix hσ τ A.1
  have hUi : (((unitAt hσ τ A)⁻¹).1).map (finPart D) = 1 := finite_part_adelic_point_matrix hσ τ (A⁻¹).1
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 (mOf A)).2.2, finite_part_block_matrix_map, hU, finPart_adj _ hUi, Matrix.map_zero _ (map_zero _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 (mOf A)).1, mR_mOf, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_matrix hσ,
        compAt_zero]
      have hUc : compAt θ τ ((unitAt hσ τ A)⁻¹).1 = (A⁻¹).1 := component_adelic_point_matrix hσ τ (A⁻¹).1
      rw [hUc]
      rfl
    · rw [(hι.2 (mOf A)).2.1 τ' e, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_ne hσ e,
        compAt_zero]
      have hUc : compAt θ τ' ((unitAt hσ τ A)⁻¹).1 = 1 := component_adelic_point_ne hσ e (A⁻¹).1
      rw [hUc, Matrix.conjTranspose_one, block_matrix_diagonal_one_eq_one]

theorem mat_nOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (y : PositivityTheory.Rg.Sw.GR n) (b : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks 1 b 0 1) : mat (ι y) = blk4 1 (atT σ τ b) 0 1 := by
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 y).2.2, finite_part_block_matrix_map, finPart_atT_map hσ τ b, Matrix.map_zero _ (map_zero _),
      Matrix.map_one _ (map_zero _) (map_one _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 y).1, hy, component_block_matrix (R := ℂ), compAt_one, compAt_atT hσ, compAt_zero]
      rfl
    · rw [(hι.2 y).2.1 τ' e, component_block_matrix (R := ℂ), compAt_one, compAt_atT_ne hσ e, compAt_zero, block_matrix_diagonal_one_eq_one]

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

