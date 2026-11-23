module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSumDecomposition
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KapBes

variable {k r : ℕ}

theorem dsigW_zero (R : Rep k r) (W : List (Mx k r)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0
    rw [ih]
    simp [PI.UpqRep.dsig]

theorem smMap_zero (R R' : Rep k r) : SmMap R R' (fun _ => 0) := by
  refine ⟨fun _ _ => R'.smSub.zero_mem, ?_, ?_, ?_⟩
  · intros
    simp
  · intros
    simp
  · intro W _
    exact ⟨0, [], by simp, fun v _ => by simp [dsigW_zero]⟩

theorem smMap_congr {R R' : Rep k r} {T T' : R.H → R'.H} (h : SmMap R R' T)
    (e : ∀ v ∈ R.sm, T' v = T v) : SmMap R R' T' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [e v hv]
    exact h.mem v hv
  · intro v hv w hw
    rw [e v hv, e w hw, e _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hv hw), h.add v hv w hw]
  · intro a v hv
    rw [e v hv, e _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a hv), h.smul a v hv]
  · intro W hW
    obtain ⟨C, Ws, h1, h2⟩ := h.cont W hW
    refine ⟨C, Ws, h1, fun v hv => ?_⟩
    change ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (T' v)‖ ≤ _
    rw [e v hv]
    exact h2 v hv

theorem smMap_sum {R R' : Rep k r}
    (hl : ∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v))
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (T : ι → R.H → R'.H) (hT : ∀ i, SmMap R R' (T i)) :
    SmMap R R' (fun v => ∑ i ∈ s, a i • T i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smMap_zero R R'
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact hl _ _ _ (hT i) ih

theorem mem_GG_of_mem_Sset {z : Fin (2 * r + k + 1) → ℂ} {s : Mx k r} (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z) :
    s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have h1 : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh.1
  have h2 : mᴴ * Formalism.QuantumDeterminants.Hpk k r * m = Formalism.QuantumDeterminants.Hpk k r := hm.1
  show (h * m)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (h * m) = Formalism.QuantumDeterminants.Hpk k r
  rw [conjTranspose_mul]
  calc mᴴ * hᴴ * Formalism.QuantumDeterminants.Hpk k r * (h * m) = mᴴ * (hᴴ * Formalism.QuantumDeterminants.Hpk k r * h) * m := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem ev_eq {ι : Type} [Fintype ι] (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) :
    ev Γ R a x = ∑ j, (star a ᵥ* Γ) j • x j := by
  unfold ev
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  rfl

theorem vecMul_inv {ι : Type} [Fintype ι] (Γ A : Matrix ι ι ℂ) (a : ι → ℂ) (hA : Aᴴ * Γ * A = Γ)
    (ha : A *ᵥ a = a) : (star a ᵥ* Γ) ᵥ* A = star a ᵥ* Γ := by
  have h : star a ᵥ* Aᴴ = star a := by rw [← star_mulVec, ha]
  conv_rhs => rw [← hA, ← vecMul_vecMul, ← vecMul_vecMul, h]

theorem main : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π om hR hRI hF hT hom I
  obtain ⟨-, -, hlin, hcw⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε mu (muI I) mu R (RI I) R hR (hRI I) hR
  obtain ⟨-, -, hlin', -⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε (muI I) mu mu (RI I) R R (hRI I) hR hR
  refine ⟨fun lI hl => ?_, fun s hs y hy => ?_, ?_⟩
  · have hP : SmMap R (RI I) (fun v => ∑ c, pr I c (tm R om v c)) :=
      smMap_congr (smMap_sum hlin Finset.univ om (pr I) (hT.pr_sm I)) (fun v hv =>
        Finset.sum_congr rfl fun c _ => (hT.pr_sm I c).smul (om c) v hv)
    obtain ⟨h1, h2, h3, h4⟩ := hl
    refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, hcw Wp _ lI hP h4⟩
    · have := hP.add v hv w hw
      simp only at this ⊢
      rw [this]; exact h1 _ (hP.mem v hv) _ (hP.mem w hw)
    · have := hP.smul c v hv
      simp only at this ⊢
      rw [this]; exact h2 c _ (hP.mem v hv)
    · have hs : h * m ∈ Formalism.QuantumDeterminants.Sset k r z := ⟨h, hh, m, hm, rfl⟩
      have e : tm R om (R.σ (h * m) v) = act ρ R (h * m) (tm R om v) := by
        funext i
        have := congrFun (hom _ hs) i
        simp only [tm, act, map_smul, smul_smul, ← Finset.sum_smul]
        rw [← this]; rfl
      have e2 := hT.pr_eq I _ (mem_GG_of_mem_Sset hs) (tm R om v)
        (fun c => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul (om c) hv)
      simp only
      rw [e, e2]
      exact h3 h hh m hm _ (hP.mem v hv)
  · have hG := mem_GG_of_mem_Sset hs
    rw [hT.io_eq I s hG y hy, ev_eq, ev_eq]
    have hv := vecMul_inv Γ (ρ s) om (hF.2.2.2.2.1 s hG) (hom s hs)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [act, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul, ← congrFun hv j]
    rfl
  · exact smMap_congr (smMap_sum hlin' Finset.univ (star om ᵥ* Γ) (io I) (hT.io_sm I))
      (fun y _ => ev_eq Γ R om _)

end GlobalTheory.KapBes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm.NabJet
open MvPowerSeries

variable {k : Type} [CommRing k] {d n : ℕ}

theorem coeff_mul_congr (N : ℕ) (f g E : PS k n d)
    (h : ∀ a : Fin n × Fin d →₀ ℕ, a.degree ≤ N → coeff a f = coeff a g)
    (a : Fin n × Fin d →₀ ℕ) (ha : a.degree ≤ N) : coeff a (f * E) = coeff a (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = a.degree := by rw [← hp', map_add (f := _)]
  rw [h p.1 (by omega)]

theorem coeff_DofN_congr (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (N : ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + 1 → coeff mo f = coeff mo g)
    (mo : Fin n × Fin d →₀ ℕ) (hmo : mo.degree ≤ N) :
    coeff mo (DofN F b v f) = coeff mo (DofN F b v g) := by
  classical
  unfold DofN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add (f := _)]
  rw [coeff_pderiv, coeff_pderiv, h]
  rw [map_add (f := _), Finsupp.degree_single]
  omega

theorem coeff_iterate_DofN_congr (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (r : ℕ) :
    ∀ (N : ℕ) (f g : PS k n d),
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo ((DofN F b v)^[r] f) = coeff mo ((DofN F b v)^[r] g) := by
  induction r with
  | zero => intro N f g h mo hmo; exact h mo hmo
  | succ r ih =>
    intro N f g h mo hmo
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih N _ _ (coeff_DofN_congr F b v (N + r) f g h) mo hmo

theorem coeff_foldr_DofN_congr (F : Fin d → PS k 2 d) {Ix : Type} (cp : Ix → Fin n) (u : Ix → Fin d → k) (m : Ix → ℕ)
    (f g : PS k n d) (L : List Ix) :
    ∀ N : ℕ,
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) g) := by
  induction L with
  | nil => intro N h mo hmo; exact h mo hmo
  | cons l L ih =>
    intro N h mo hmo
    rw [List.foldr_cons, List.foldr_cons]
    refine coeff_iterate_DofN_congr F (cp l) (u l) (m l) N _ _ (ih (N + m l) fun mo' h' => h mo' ?_) mo hmo
    rw [List.map_cons, List.sum_cons]
    omega

theorem constantCoeff_DmonN_congr (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ m.degree → coeff mo f = coeff mo g) :
    constantCoeff (DmonN F cp u m f) = constantCoeff (DmonN F cp u m g) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  unfold DmonN
  refine coeff_foldr_DofN_congr F cp u m f g _ 0 (fun mo' h' => h mo' ?_) 0 (by simp)
  rwa [Finset.sum_map_toList, ← Finsupp.degree_eq_sum, zero_add] at h'

theorem isLinearMap_DofN (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) :
    IsLinearMap k (DofN F b v : PS k n d → PS k n d) := by
  constructor
  · intro f g
    unfold DofN
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
  · intro c f
    unfold DofN
    simp only [Derivation.map_smul, mul_smul_comm, Finset.smul_sum]

theorem isLinearMap_iterate {M : Type} [AddCommGroup M] [Module k M] (φ : M → M) (hφ : IsLinearMap k φ) (r : ℕ) :
    IsLinearMap k φ^[r] := by
  induction r with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ r ih =>
    constructor
    · intro f g
      simp only [Function.iterate_succ_apply, hφ.map_add (f := _), ih.map_add (f := _)]
    · intro c f
      simp only [Function.iterate_succ_apply, hφ.map_smul, ih.map_smul]

theorem isLinearMap_DmonN (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) : IsLinearMap k (DmonN F cp u m : PS k n d → PS k n d) := by
  unfold DmonN
  induction (Finset.univ : Finset Ix).toList with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons l L ih =>
    have hl := isLinearMap_iterate _ (isLinearMap_DofN F (cp l) (u l)) (m l)
    constructor
    · intro f g
      simp only [List.foldr_cons]
      rw [ih.map_add (f := _), hl.map_add (f := _)]
    · intro c f
      simp only [List.foldr_cons]
      rw [ih.map_smul, hl.map_smul]

theorem constantCoeff_DpolyN_eq (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (P : MvPolynomial Ix k) (f : PS k n d) (S : Finset (Ix →₀ ℕ)) (hS : P.support ⊆ S) :
    constantCoeff (DpolyN F cp u P f) = ∑ m ∈ S, P.coeff m * constantCoeff (DmonN F cp u m f) := by
  unfold DpolyN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, constantCoeff_C]
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]

end GlobalTheory.PowGerm.NabJet

namespace GlobalTheory.PowGerm
open MvPowerSeries

theorem nabJet : NabJetSt := by
  intro R _ d O _ _ B k _ _ _ h w0 q n Ix _ cp u
  classical
  refine ⟨fun P f g hfg => ?_, fun P J _ c f => ?_, fun f J _ c P => ?_⟩
  · unfold nabValN
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    refine NabJet.constantCoeff_DmonN_congr _ cp u m _ _ fun mo hmo => ?_
    refine NabJet.coeff_mul_congr P.totalDegree f g _ hfg mo (hmo.trans ?_)
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.degree_apply]
  · unfold nabValN
    simp only [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hl := NabJet.isLinearMap_DmonN (B.FK k) cp u m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, ← IsLinearMap.mk'_apply hl, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, IsLinearMap.mk'_apply, smul_eq_C_mul, map_mul, constantCoeff_C]
    ring
  · unfold nabValN
    set S : Finset (Ix →₀ ℕ) := (∑ j, c j • P j).support ∪ Finset.univ.biUnion fun j => (P j).support with hS
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u _ _ S Finset.subset_union_left]
    have hj : ∀ j, (P j).support ⊆ S := fun j =>
      (Finset.subset_biUnion_of_mem (fun j => (P j).support) (Finset.mem_univ j)).trans Finset.subset_union_right
    simp only [fun j => NabJet.constantCoeff_DpolyN_eq (B.FK k) cp u (P j)
      (f * FB.expS k ((q : k) • ∑ b, ev ![pt k d b] (B.hL k h w0))) S (hj j), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, _root_.mul_assoc]

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompExpIteratedDerivBounded
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology

theorem cutoff_comp_exp_iteratedDeriv_bounded (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv p (fun t => χ (Real.exp t)) t| ≤ C := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hc : ∀ k t : ℝ, iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
    intro k t
    cases p with
    | zero => simp
    | succ n => simp [iteratedDeriv_succ']
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hs.comp Real.contDiff_exp
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log δ → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have := Real.exp_lt_exp.mpr hs
      rw [Real.exp_log hδ] at this
      simp only [hh, h0 _ this]
    rw [this.iteratedDeriv_eq p, hc]; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, h1 _ this]
    rw [this.iteratedDeriv_eq p, hc]
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log δ) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C0 1, le_trans zero_le_one (le_max_right _ _), fun t => ?_⟩
  rcases lt_or_ge t (Real.log δ) with h1 | h1
  · rw [hlow t h1]; simp
  · rcases lt_or_ge 0 t with h2 | h2
    · rw [hhigh t h2]; split_ifs <;> simp
    · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)

theorem ld_cut_pow_bound (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (e j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  choose B hB0 hB using cutoff_comp_exp_iteratedDeriv_bounded χ hχ
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * (e : ℝ) ^ (j - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB0 i)) (by positivity), ?_⟩
  intro ε x hε hx
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hχ.1.comp Real.contDiff_exp
  unfold LE.ld
  have e1 : (fun u : ℝ => χ (Real.exp u / ε) * Real.exp u ^ e) =
      fun u : ℝ => h (u - Real.log ε) * Real.exp ((e : ℝ) * u) := by
    funext u
    simp only [hh]
    rw [Real.exp_sub, Real.exp_log hε, Real.exp_nat_mul]
  have c1 : ContDiff ℝ j (fun u : ℝ => h (u - Real.log ε)) :=
    (hsm.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have c2 : ContDiff ℝ j (fun u : ℝ => Real.exp ((e : ℝ) * u)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  beta_reduce
  rw [e1, iteratedDeriv_fun_mul c1.contDiffAt c2.contDiffAt, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [iteratedDeriv_comp_sub_const, iteratedDeriv_exp_const_mul]
  beta_reduce
  rw [Real.exp_nat_mul, Real.exp_log hx, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j.choose i : ℝ)),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (e : ℝ) ^ (j - i) * x ^ e), ← mul_assoc]
  have := hB i (Real.log x - Real.log ε)
  gcongr

theorem ld_cut_pow : ∀ (χ : ℝ → ℝ) (e J : ℕ), C6.IsCut0 χ →
    (∀ ε : ℝ, 0 < ε → CutPow e fun y => χ (y / ε) * y ^ e) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → ∀ j, j ≤ J →
        |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  intro χ e J hχ
  constructor
  · intro ε hε
    obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
    refine ⟨(hs.comp (contDiff_id.div_const ε)).mul (contDiff_id.pow e), ⟨δ * ε, by positivity, fun x hx => ?_⟩,
      1, ε, fun x hx => ?_⟩
    · have : x / ε < δ := by rwa [div_lt_iff₀ hε]
      simp [h0 _ this]
    · have : 1 ≤ x / ε := by rwa [le_div_iff₀ hε, one_mul]
      simp [h1 _ this]
  · choose C hC0 hC using ld_cut_pow_bound χ hχ e
    refine ⟨∑ j ∈ Finset.range (J + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun ε x hε hx j hj => ?_⟩
    refine (hC j ε x hε hx).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr (by omega))

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnits
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_expand_units {n : ℕ} (Q Y : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) :
    Y = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have h2 : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q)
      = Q⁻¹ * (∑ a, ∑ b, Matrix.single a b ((Q * Y * Q⁻¹) a b)) * Q := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h2, ← Matrix.matrix_eq_sum_single]
  calc Y = (Q⁻¹ * Q) * Y * (Q⁻¹ * Q) := by rw [h1]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_units_mul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = (if b = c then (1 : ℂ) else 0) • (Q⁻¹ * Matrix.single a d (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have : (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = Q⁻¹ * (Matrix.single a b (1 : ℂ) * (Q * Q⁻¹) * Matrix.single c d (1 : ℂ)) * Q := by
    simp only [Matrix.mul_assoc]
  rw [this, h1, Matrix.mul_one]
  by_cases h : b = c
  · subst h
    simp [Matrix.single_mul_single_same]
  · simp [h, Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem dC_expand_units : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  intro hK k r ε mu R hR Q E hQ hE
  obtain ⟨-, -, hlin, hX, hbr, -⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hL : ∀ v : R.smSub, ∃ L : Mx k r →ₗ[ℂ] R.H, ∀ Y, L Y = R.dC Y v := by
    intro v
    have hv : (v : R.H) ∈ R.sm := v.2
    have h0 : R.dC 0 v = 0 := by
      have := hlin 0 0 1 v hv
      simpa using this
    refine ⟨{ toFun := fun Y => R.dC Y v, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro Y Z
      simpa using hlin Y Z 1 v hv
    · intro a Y
      simpa [h0] using hlin Y 0 a v hv
  have hexp : ∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
    intro Y v
    obtain ⟨L, hLv⟩ := hL v
    rw [← hLv]
    conv_lhs => rw [conj_expand_units Q Y hQ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
    simp only [hLv, hE _ _ v]
  refine ⟨?_, hexp, fun X hXl v => ?_⟩
  · intro a b c d
    ext v
    obtain ⟨L, hLv⟩ := hL v
    have := hbr (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v v.2
    rw [conj_units_mul Q hQ, conj_units_mul Q hQ, ← hLv (_ - _), map_sub, map_smul, map_smul, hLv, hLv,
      ← hE, ← hE, ← hE, ← hE, ← hE, ← hE] at this
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [this]
    congr 1 <;> split_ifs <;> simp_all
  · rw [← hX X hXl v v.2, hexp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsPassGeneratorsStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators | exact GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators <;> assumption)
end

