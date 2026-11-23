module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0020
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0016
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0021
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddA

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

theorem oneD : OneD := by
  intro F _ _ hF ψ hψ S ε hε ν hν
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨db, hdb⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne F
  obtain ⟨⟨laminf, hinf⟩, hlamex⟩ := _root_.GlobalTheory.CompanionTheory.SW.StdEx.exists_std F
  choose lam hlam using hlamex
  obtain ⟨S₁, hS₁⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.exists_test_approx F hF ψ hψ db hdb laminf lam hinf hlam
  obtain ⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, -, hlim⟩ := hS₁ (S ∪ S₁) Finset.subset_union_right
  haveI : db.IsAddHaarMeasure := hdb.1
  have hεε := idF_mul hε
  have hp : Continuous (AddMonoidHom.mulLeft ε) := continuous_const.mul continuous_id
  have hpp : ∀ x, AddMonoidHom.mulLeft ε (AddMonoidHom.mulLeft ε x) = AddMonoidHom.mulLeft ε x := fun x => by
    simp only [AddMonoidHom.coe_mulLeft, ← mul_assoc, hεε]
  have hcY : IsClosed (((AddMonoidHom.mulLeft ε).ker : Set (AF F))) := isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace (AddMonoidHom.mulLeft ε).ker := hcY.locallyCompactSpace
  haveI : LocallyCompactSpace (fixE ε) := (isClosed_eq hp continuous_id).locallyCompactSpace
  haveI := hν
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (AddMonoidHom.mulLeft ε).ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (fixE ε) := inferInstance
  haveI : SigmaCompactSpace (AddMonoidHom.mulLeft ε).ker := inferInstance
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨c, hc, hdec⟩ := decomp (AddMonoidHom.mulLeft ε) hp hpp db ν (Measure.addHaar)
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  have hne : ∀ k, ∫ y, testT (ρ k) (S ∪ S₁) (U k) y ∂db ≠ 0 := by
    intro k
    rw [hint k]
    refine mul_ne_zero (by exact_mod_cast (hρ k).2.2.2.ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    have h1 : 0 < (lam v) (U k v) := (hU k v).2.1.measure_pos (lam v) ⟨0, (hU k v).2.2⟩
    have h2 : (lam v) (U k v) ≠ ⊤ := (hU k v).1.measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  choose g Gc hGc hgI hgb hgint hgeq using fun k => kdata ψ hψ Finset.subset_union_left hε db ν Measure.addHaar c hc
    hdec (ρ k) (hρ k).1 (hρ k).2.1 (hρ k).2.2.1 (U k) (fun v => (hU k v).2.2) (hinv k).1 (hinv k).2 (hne k)
  refine ⟨g, fun k s => Gc k * tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)),
    fun k => {a | ε * a = a ∧ fstA F a ∈ tsupport (ρ k) ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v},
    fun k => ⟨hgI k, hgb k, fun s => ⟨mul_nonneg (hGc k) (tR_nonneg (hρ k).2.2.1 _ _ _), hgint k s⟩⟩,
    fun h => ?_, fun k s hs => ?_, top1 S ε hε _ U hρt hUt⟩
  · have hl := hlim h.1
    have hm : sndA F h.1 ∈ intF (S ∪ S₁) := fun v hv => by
      rw [snd_eq, fix_snd hε (memH h) (fun h' => hv (Finset.mem_union_left _ h'))]
      exact zero_mem _
    rw [Set.indicator_of_mem hm] at hl
    simp only [hgeq]
    exact hl
  · have ht : tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)) ≠ 0 := fun h0 => hs (by simp only [h0, mul_zero])
    unfold tR at ht
    have hρne : ρ k (fstA F (-(ε * s))) ≠ 0 := fun h0 => ht (by rw [h0, zero_mul])
    have hbox : sndA F (-(ε * s)) ∈ boxA (S ∪ S₁) (U k) := by
      by_contra hn
      exact ht (by rw [Set.indicator_of_notMem hn, mul_zero])
    exact ⟨by rw [mul_neg, ← mul_assoc, hεε], subset_tsupport _ hρne,
      fun v hv => hbox.1 v (Finset.mem_union_left _ hv)⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLow
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem cutR_left {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) :
    LeftInv (GF D n) (cutR nb C F) := fun γ hγ g => by
  unfold cutR
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, hinv γ hγ]

theorem cutR_cont {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hF : Continuous F) :
    Continuous (cutR nb C F) := by
  unfold cutR
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (hF.comp (continuous_id.mul continuous_const))

theorem cutR_lev {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {F : G D n → ℂ}
    (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) {k : G D n} (hk : k ∈ lev nb C.s)
    (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) (g : G D n) : cutR nb C F (g * k) = cutR nb C F g := by
  unfold cutR
  refine Finset.sum_congr rfl fun x hx => ?_
  have e : g * k * nb x = g * nb x * ((nb x)⁻¹ * k * nb x) := by group
  rw [e, hK _ (conj_mem_KAt hnb C hk hkv hx)]

theorem fc_cutR_low {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g)
    (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) (β : HermE D n) (hβ : β.1.rank < r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : fc ψ lam 𝓖 nb (cutR nb C F) β g = 0 := by
  rw [fc_cutR hψ hC hF hinv C β hg]
  by_cases h : ∀ x : hermA D n, IntAt v x → pch ψ x.1 (rat β.1) = 1
  · rw [hkill β hβ h, zero_mul]
  · push Not at h
    obtain ⟨x, hx, hne⟩ := h
    have e := fc_fix hψ hC hinv hK β hx hg
    have h0 : (1 - pch ψ x.1 (rat β.1)) * fc ψ lam 𝓖 nb F β g = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]

theorem vanish_at {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hFP : FourierPt) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) {F : G D n → ℂ} (hF : Continuous F)
    (hinv : LeftInv (GF D n) F) (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (hR : RankLT ψ F r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : cutR nb C F g = 0 := by
  obtain ⟨lam, 𝓖, hcov⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hcov⟩
  have hco : ∀ β : HermE D n, ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = 0 := by
    intro β
    have e : ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = fc ψ lam 𝓖 nb (cutR nb C F) β g := by
      rw [fc_eq]
      refine integral_congr_ae (.of_forall fun b => ?_)
      show _ * conj (pch ψ b.1 (rat β.1)) = _ * chn ψ β b
      rw [pch_rat, conj_psi hψ, chn_eq]
    rw [e]
    by_cases hβ : β.1.rank < r
    · exact fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg
    · rw [fc_cutR hψ hC hF hinv C β hg, hR nb lam 𝓖 hC β (not_lt.1 hβ) g, mul_zero]
  have key := hFP D n ψ hψ lam 𝓖 hcov (fun b => cutR nb C F (nb b * g)) (cont_nb (cutR_cont C hF) hnb g)
    (fun γ hγ b => per_nb (cutR_left C hinv) hnb g γ hγ b) hco
  have h0 := congrFun key 0
  simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
  exact h0

end PositivityTheory.Rg.Rsw.L.LCutLow

namespace PositivityTheory.Rg.Rsw.L

open LCutLow in
theorem cutLow : FourierPt → WeakApproximationFinitePlace → CutLow := by
  intro hFP hWA D n r ψ hψ nb hnb v C hkill F hF hinv hK
  have hlev : ∀ k ∈ lev nb C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, cutR nb C F (g * k) = cutR nb C F g :=
    fun k hk hkv g => cutR_lev hnb C hK hk hkv g
  refine ⟨fun hR => ?_, ⟨lev nb C.s, isOpen_lev nb C.s, hlev⟩, fun lam 𝓖 hC β g hg =>
    ⟨fc_cutR hψ hC hF hinv C β hg, fun hβ => fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg⟩⟩
  funext g
  obtain ⟨γ, hγ, g', hg', k, hk, hkv, rfl⟩ := hWA D n v (lev nb C.s) (isOpen_lev nb C.s) g
  show cutR nb C F (γ * g' * k) = 0
  rw [hlev k hk hkv, cutR_left C hinv γ hγ g']
  exact vanish_at hψ hFP hnb C hkill hF hinv hK hR hg'

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem mtL_mul (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mtL_one (V : HSp D) : mt V 1 = 1 := rfl

theorem finPart_mtL {V : HSp D} {a : GA D V} (ha : a ∈ GinfC V) : (mt V a).map (finPart D) = 1 := by
  have h0 : finHom V a = 1 := ha
  have h1 : (finHom V a).1 = 1 := by rw [h0]; rfl
  exact h1

theorem den_finL {ι : Type} [Fintype ι] (z : ι → Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, N • z i ∈ intAE D := by
  classical
  choose N hN hNz using fun i => GlobalTheory.CompanionTheory.Ipf.Bdd.den_one (D := D) (z i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (hNz i) _

theorem compAt_mt_GfC (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V k) = 1 := by
  have h0 : infHom V k = 1 := hk
  have h : (mt V k).map (infPart D) = 1 := by
    have h1 : (infHom V k).1 = 1 := by rw [h0]; rfl
    exact h1
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij
  simp only [compAt, Matrix.map_apply, hij, Matrix.one_apply]
  split_ifs <;> simp

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gen_bound_col {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (y : GA D V)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ a ∈ GinfC V, ∀ k ∈ GfC V, (∀ i j, finPart D (mt V k⁻¹ i j) ∈ intAE D) →
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
        ‖f (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x.1)) i j) *
          g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x.1)) i j))‖ₑ ≤ C := by
  obtain ⟨Mg, hMg⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.CompanionTheory.Ipf.Bdd.exists_den_matrix (D := D) (a := V.rank) (b := n) (K := tsupport g) hg.2
  obtain ⟨M, hM, hMy⟩ := den_finL (D := D)
    (fun p : Fin V.rank × Fin V.rank => finPart D (mt V y⁻¹ p.1 p.2))
  obtain ⟨C₀, hC₀⟩ := fullRank_col D V.rank n (N * M) (Nat.mul_pos hN hM) f
  refine ⟨ENNReal.ofReal C₀ * ENNReal.ofReal Mg, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
    fun a ha k hk hki => ?_⟩
  set B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => compAt θ τ (mt V (a * y)) with hBdef
  have hB : ∀ τ, ‖(B τ).det‖ = 1 := fun τ => GlobalTheory.CompanionTheory.Ipf.Bdd.norm_det_compAt hθ τ V (a * y)
  have hmt : mt V (k * a * y) = mt V k * mt V (a * y) := by
    rw [mul_assoc, mtL_mul]

  have hinf : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x)) i j) = fun τ => B τ * x.map (tauE D τ) := by
    intro x
    funext τ i j
    have e1 := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_mulM θ τ (mt V (k * a * y)) (rat x)
    have e2 := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_mulM θ τ (mt V k) (mt V (a * y))
    have e0 : compAt θ τ (rat x) = x.map (tauE D τ) := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_rat hθ τ x
    rw [e0] at e1
    rw [compAt_mt_GfC θ V hk τ, Matrix.one_mul] at e2
    have e4 : compAt θ τ (mt V (k * a * y)) = B τ := by
      rw [hmt]; exact e2
    have e3 : compAt θ τ (mm (mt V (k * a * y)) (rat x)) = B τ * x.map (tauE D τ) := by
      rw [← e4]; exact e1
    rw [e3]

  set Yf : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V y).map (finPart D) with hYf
  set Yi : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V y⁻¹).map (finPart D) with hYi
  set Kf : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V k).map (finPart D) with hKf
  set Ki : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V k⁻¹).map (finPart D) with hKi
  have hYY : Yi * Yf = 1 := by
    rw [hYi, hYf, ← Matrix.map_mul, ← mtL_mul, inv_mul_cancel, mtL_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hKK : Ki * Kf = 1 := by
    rw [hKi, hKf, ← Matrix.map_mul, ← mtL_mul, inv_mul_cancel, mtL_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hfin : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      (mm (mt V (k * a * y)) (rat x)).map (finPart D) = Kf * Yf * x.map (fun c => finPart D (incA D c)) := by
    intro x
    have : (mt V (a * y)).map (finPart D) = Yf := by
      rw [mtL_mul, Matrix.map_mul, finPart_mtL ha, Matrix.one_mul]
    show (mt V (k * a * y) * rat x).map (finPart D) = _
    rw [Matrix.map_mul, hmt, Matrix.map_mul, this]
    rfl

  have hden : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j)) ≠ 0 →
        ∀ i j, ((N * M : ℕ) : D.host.E) * x i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D := by
    intro x hx i j
    set Z : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) :=
      (mm (mt V (k * a * y)) (rat x)).map (finPart D) with hZ
    have hZK : Z ∈ tsupport g := subset_tsupport _ hx
    have hxZ : x.map (fun c => finPart D (incA D c)) = Yi * (Ki * Z) := by
      rw [hZ, hfin x, ← Matrix.mul_assoc Ki, ← Matrix.mul_assoc Ki, hKK, Matrix.one_mul, ← Matrix.mul_assoc,
        hYY, Matrix.one_mul]
    refine GlobalTheory.CompanionTheory.Ipf.Bdd.mem_intR_of_finPart ?_
    have e : finPart D (incA D (((N * M : ℕ) : D.host.E) * x i j)) =
        ∑ l, ∑ m, (M • Yi i l) * (Ki l m * (N • Z m j)) := by
      have hij : finPart D (incA D (x i j)) = (Yi * (Ki * Z)) i j := by
        rw [← hxZ]; rfl
      rw [map_mul, map_mul, hij, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [map_natCast, nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    refine sum_mem fun l _ => sum_mem fun m _ => ?_
    exact GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hMy (i, l)) (GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hki l m) (hNK Z hZK m j))

  set S₁ : Set (Matrix (Fin V.rank) (Fin n) D.host.E) := {x | x.rank = V.rank} with hS₁
  set S₂ : Set (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    {x | x.rank = V.rank ∧ ∀ i j, ((N * M : ℕ) : D.host.E) * x i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D} with hS₂
  set F : Matrix (Fin V.rank) (Fin n) D.host.E → ℝ≥0∞ := fun x =>
    ‖f (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x)) i j) *
      g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j))‖ₑ with hF
  set G : Matrix (Fin V.rank) (Fin n) D.host.E → ℝ≥0∞ := fun x =>
    ‖f (fun τ => B τ * x.map (tauE D τ))‖ₑ * ENNReal.ofReal Mg with hG
  have e1 : ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F x.1 = ∑' x, S₁.indicator F x :=
    tsum_subtype S₁ F
  have e2 : ∑' x : S₂, G x.1 = ∑' x, S₂.indicator G x := tsum_subtype S₂ G
  have hle : ∀ x, S₁.indicator F x ≤ S₂.indicator G x := by
    intro x
    by_cases h1 : x ∈ S₁
    · rw [Set.indicator_of_mem h1]
      by_cases h0 : g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j)) = 0
      · have : F x = 0 := by simp only [hF, h0, mul_zero, enorm_zero]
        rw [this]; exact zero_le
      · have h2 : x ∈ S₂ := ⟨h1, hden x h0⟩
        rw [Set.indicator_of_mem h2]
        simp only [hF, hG]
        rw [hinf x, enorm_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hMg _)
    · rw [Set.indicator_of_notMem h1]; exact zero_le
  show ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F x.1 ≤ _
  rw [e1]
  calc ∑' x, S₁.indicator F x ≤ ∑' x, S₂.indicator G x := ENNReal.tsum_le_tsum hle
    _ = ∑' x : S₂, G x.1 := e2.symm
    _ = (∑' x : S₂, ‖f (fun τ => B τ * x.1.map (tauE D τ))‖ₑ) * ENNReal.ofReal Mg := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal Mg := by
        gcongr
        exact hC₀ B hB

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBdd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {θ : InfFam D} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem bound_all {v : Pl D} (U : Subgroup (G D n)) (hUo : IsOpen (U : Set (G D n))) (Φ : schwartzA θ W.rank n)
    (hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Φ (γ * g) h = theta ω Φ g h)
    (hfix : ∀ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Φ = Φ)
    (hU : ∀ k k' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k' →
      k ∈ U → k' ∈ U)
    (hdec : ∀ g : G D n, ∃ γ ∈ GF D n, ∃ g' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g' = 1 ∧
      ∃ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} ∧ g = γ * g' * k)
    (hb : ∀ Q : Set (G D n), IsCompact Q → ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 →
      ∀ h, ‖theta ω Φ g h‖ ≤ b)
    (K₀ : Set (G D n)) (hK₀ : IsCompact K₀) : ∃ b : ℝ, ∀ g ∈ K₀, ∀ h, ‖theta ω Φ g h‖ ≤ b := by
  have hred : ∀ γ ∈ GF D n, ∀ g' k, k ∈ U → k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ h,
      theta ω Φ (γ * g' * k) h = theta ω Φ g' h := by
    intro γ hγ g' k hk hkv h
    rw [mul_assoc, hrat γ hγ]
    unfold theta
    rw [map_mul, Module.End.mul_apply, hfix k hk hkv]
  choose γf hγf g'f hg'f kf hkf hkvf hgf using hdec
  obtain ⟨W₀, hW₀c, hW₀1, hW₀U⟩ := exists_compact_subset hUo (one_mem U)
  have hW₀n : W₀ ∈ 𝓝 (1 : G D n) := mem_interior_iff_mem_nhds.1 hW₀1
  have hN : ∀ g₀ : G D n, {g | g₀⁻¹ * g ∈ W₀} ∈ 𝓝 g₀ := fun g₀ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW₀n)
  obtain ⟨t, -, hcov⟩ := hK₀.elim_nhds_subcover (fun g₀ => {g | g₀⁻¹ * g ∈ W₀}) fun g₀ _ => hN g₀
  let τ : G D n → G D n := fun ε => ε * (locPart v ε)⁻¹
  have hτ : Continuous τ := continuous_id.mul ((continuous_locPart v).inv)
  let Q : Set (G D n) := ⋃ g₀ ∈ t, (fun ε => g'f g₀ * τ ε) '' W₀
  have hQ : IsCompact Q := t.isCompact_biUnion fun g₀ _ => hW₀c.image (continuous_const.mul hτ)
  obtain ⟨b, hb'⟩ := hb Q hQ
  refine ⟨b, fun g hg h => ?_⟩
  obtain ⟨g₀, hg₀t, hgg₀⟩ := Set.mem_iUnion₂.1 (hcov hg)
  set ε := g₀⁻¹ * g with hε
  have hεW : ε ∈ W₀ := hgg₀
  set εv := locPart v ε with hεv
  set ε' := τ ε with hε'
  have hpv : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ε' = 1 := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v (ε * (locPart v ε)⁻¹) = 1
    rw [map_mul, map_inv, proj_locPart, mul_inv_cancel]
  have hc : kf g₀ * ε' = ε' * kf g₀ := commute_of_atPts (hkvf g₀) hpv
  have hsplit : ε' * εv = ε := by
    show ε * (locPart v ε)⁻¹ * locPart v ε = ε
    group
  have hkU : kf g₀ * εv ∈ U := mul_mem (hkf g₀) (hU ε εv (proj_locPart v ε).symm (hW₀U hεW))
  have hkv : kf g₀ * εv ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem (hkvf g₀) (locPart_mem_atPts v ε)
  have heq : g = γf g₀ * (g'f g₀ * ε') * (kf g₀ * εv) := by
    calc g = g₀ * ε := by rw [hε]; group
      _ = γf g₀ * g'f g₀ * kf g₀ * (ε' * εv) := by rw [← hgf g₀, hsplit]
      _ = γf g₀ * g'f g₀ * (kf g₀ * ε') * εv := by simp only [mul_assoc]
      _ = γf g₀ * g'f g₀ * (ε' * kf g₀) * εv := by rw [hc]
      _ = _ := by simp only [mul_assoc]
  rw [heq, hred _ (hγf g₀) _ _ hkU hkv]
  refine hb' _ (Set.mem_iUnion₂.2 ⟨g₀, hg₀t, ε, hεW, rfl⟩) ?_ h
  rw [map_mul, hg'f g₀, hpv, one_mul]

end PositivityTheory.Rg.Rsw.L.LThBdd

namespace PositivityTheory.Rg.Rsw.L

open LThBdd in
theorem thBdd : WMaj → LatBound → WeakApproximationFinitePlace → ThBdd := by
  intro hWM hLB hWA D n W ψ hψ χ hχ hη θ hθ μ hμ ω hω nb hnb v C hC Ψ Ψ' hΨ hΨ'
  obtain ⟨𝓕, hμ'⟩ := hμ
  have hW := hWM D n W ψ hψ χ hχ hη θ hθ μ ⟨𝓕, hμ'⟩ ω hω Ψ'
  have hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Ψ' (γ * g) h = theta ω Ψ' g h :=
    fun γ hγ g h => theta_rat hψ hχ hθ hμ' hω Ψ' hγ g h
  have hfix : ∀ k ∈ Ucut nb v C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Ψ' = Ψ' :=
    fun k hk hkv => fix_open hnb C Ψ Ψ' hΨ hΨ' hk hkv
  refine ⟨theta_cont hθ Ψ' hW.1 hW.2, hrat, ⟨Ucut nb v C.s, isOpen_Ucut _ _ _, hfix⟩, fun K₀ hK₀ => ?_,
    fun x g hg => ⟨omega_cut hω hnb C Ψ Ψ' hΨ' hg, theta_nb hω hnb C hC Ψ Ψ' hΨ hΨ' x hg⟩⟩
  exact bound_all (Ucut nb v C.s) (isOpen_Ucut _ _ _) Ψ' hrat hfix (fun k k' e hk => mem_Ucut_of_proj e hk)
    (fun g => hWA D n v (Ucut nb v C.s) (isOpen_Ucut _ _ _) g)
    (bound_triv hω hnb C hC Ψ Ψ' hΨ hΨ' hLB hθ hW.2) K₀ hK₀

end PositivityTheory.Rg.Rsw.L

end
end

