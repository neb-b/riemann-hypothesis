module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0005
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFrameEntryRelation
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselIntertwine

theorem bessel_dsig (hK : PI.KFinSmooth) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {l : R.H → Wp} (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hl : IsBes R z π l) {X : Mx k r} (hX : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X) (hX' : PI.UpqRep.InLieHpk k r X)
    {v : R.H} (hv : v ∈ R.sm) :
    l (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = Formalism.FourierDecayAlt.Q.dRep π X (l v) := by
  have hd := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 v hv).2 X hX'
  have h1 : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Formalism.QuantumDeterminants.UH]
    · intro a i _
      simp [Matrix.one_apply]
    · intro i j _ _ _
      simp [Matrix.one_apply]
  have he : (fun t : ℝ => l (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) =
      fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (l v) := by
    funext t
    have := hl.2.2.1 _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) 1 h1 v hv
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.Qx8.psi_one hz, one_smul] at this
    exact this
  rw [he] at hd
  exact hd.deriv.symm

theorem bessel_intertwines_glW : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsBes R z π l → ∀ i j : Fin k, ∀ v ∈ R.sm, l (R.dC (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) v) = Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) (l v) := by
  intro hK k r ε mu R hR Wp _ _ _ _ z π l g hz hT hg hl i j v hv
  obtain ⟨hF, hU⟩ := (_root_.GlobalTheory.CapFrame.frame_matrix_units k r z g hz hT hg).2.2.1
  rw [← hU i j]
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.QrD.frame_lie hF i j
  set Y := Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) _ i j with hY
  have hinv : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r :=
    Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have e1 : (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) =
      Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) Y := by
    rw [Formalism.QuantumDeterminants.hpart1, hinv, sub_eq_add_neg]
  have e2 : (1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) =
      Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) Y := by
    rw [Formalism.QuantumDeterminants.hpart2, hinv, sub_neg_eq_add]
  have l1 : PI.UpqRep.InLieHpk k r (Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) Y) := h1.1.1
  have l2 : PI.UpqRep.InLieHpk k r (Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) Y) := h2.1.1
  have s1 := ((GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR _ l1).1 v hv).1
  have s2 := ((GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR _ l2).1 v hv).1
  rw [Rep.dC, e1, e2, hl.1 _ s1 _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ s2), hl.2.1 _ _ s2,
    bessel_dsig hK hR hz hl h1 l1 hv, bessel_dsig hK hR hz hl h2 l2 hv]
  rfl

end GlobalTheory.BesselIntertwine
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapGrowthBoundStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_integral_equivariant_of_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (g * m) w) v = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  first | exact @GlobalTheory.BesselEquiv.be_equivariant | exact GlobalTheory.BesselEquiv.be_equivariant | (intros; apply GlobalTheory.BesselEquiv.be_equivariant <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapPairingStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_gap_pairing : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  first | exact @GlobalTheory.besselIntegral_sesquilinear | exact GlobalTheory.besselIntegral_sesquilinear | (intros; apply GlobalTheory.besselIntegral_sesquilinear <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSumDecomposition
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
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
  refine ⟨fun _ _ => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_zero R'.σ, ?_, ?_, ?_⟩
  · intros
    simp
  · intros
    simp
  · intro W _
    exact ⟨0, [], by simp, fun _ _ => by simp [dsigW_zero]⟩

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
    exact ⟨C, Ws, h1, fun v hv => by
      have := h2 v hv
      simp only at this ⊢
      rw [e v hv]; exact this⟩

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

theorem main : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) := by
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
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsUnitary
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapUnitary

theorem diag_single {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    PI.UpqRep.Jm ε * Matrix.single b a (1 : ℂ) * PI.UpqRep.Jm ε
      = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Matrix.single b a (1 : ℂ) := by
  ext i j
  unfold PI.UpqRep.Jm Formalism.REAL.sgn
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

theorem adj_unit {n : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n) :
    (Qᴴ * PI.UpqRep.Jm ε * Q) * (Q⁻¹ * Matrix.single a b 1 * Q)ᴴ * (Qᴴ * PI.UpqRep.Jm ε * Q)
      = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • (Q⁻¹ * Matrix.single b a 1 * Q) := by
  have h1 : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ
  have hi : Q⁻¹ = Qᴴ := Matrix.inv_eq_right_inv h1
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Q * (Qᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_single, star_one, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diag_single]
  simp only [Matrix.mul_assoc, h2]

theorem isUnitary_of_isE : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  intro hK k r ε mu R hR Q E hQ hE a b x y
  obtain ⟨-, -, hlin, -, -, hadj⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * PI.UpqRep.Jm ε * Q := hQ.1.2.symm
  have h0 : R.dC 0 (y : R.H) = 0 := by
    have := hlin 0 0 1 y y.2
    simpa using this
  have hs : ∀ (c : ℂ) Y, R.dC (c • Y) (y : R.H) = c • R.dC Y (y : R.H) := fun c Y => by
    have := hlin Y 0 c y y.2
    rwa [add_zero, h0, add_zero] at this
  rw [Submodule.coe_inner, Submodule.coe_inner, hE, hE, hadj _ _ x.2 _ y.2, hH, adj_unit ε Q hQ.2, hs,
    inner_smul_right]

end GlobalTheory.CapUnitary
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionExpandMatrixUnits
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_expand_units {n : ℕ} (Q Y : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) :
    Y = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hl : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have key : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q)
      = Q⁻¹ * (∑ a, ∑ b, (Q * Y * Q⁻¹) a b • Matrix.single a b (1 : ℂ)) * Q := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hM : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • Matrix.single a b (1 : ℂ) = Q * Y * Q⁻¹ := by
    conv_rhs => rw [Matrix.matrix_eq_sum_single (Q * Y * Q⁻¹)]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [key, hM]
  simp only [Matrix.mul_assoc, hl, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hl, Matrix.one_mul]

theorem conj_units_mul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = (if b = c then (1 : ℂ) else 0) • (Q⁻¹ * Matrix.single a d (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hr : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have e1 : (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = Q⁻¹ * (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ)) * Q := by
    calc (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
        = Q⁻¹ * (Matrix.single a b (1 : ℂ) * ((Q * Q⁻¹) * Matrix.single c d (1 : ℂ))) * Q := by
          simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ)) * Q := by
          rw [hr, Matrix.one_mul]
  rw [e1]
  by_cases hbc : b = c
  · subst hbc
    simp [Matrix.single_mul_single_same]
  · rw [Matrix.single_mul_single_of_ne (1 : ℂ) a b c hbc (1 : ℂ)]
    simp [hbc]

theorem dC_expand_units : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  intro hK k r ε mu R hDG Q E hQ hE
  obtain ⟨-, -, hlinY, hLie, hbr, -⟩ := Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hDG
  have hv0 : ∀ v : R.smSub, (v : R.H) ∈ R.sm := fun v => v.2
  have hE' : ∀ (a b : Fin (2 * r + k + 1)) (v : R.smSub),
      ((E a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) v := hE
  have h0 : ∀ v : R.smSub, R.dC 0 (v : R.H) = 0 := fun v => by
    have := hlinY 0 0 1 v (hv0 v)
    simpa using this
  let f : R.smSub → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ] R.H := fun v =>
    { toFun := fun Y => R.dC Y v
      map_add' := fun Y Z => by
        have := hlinY Y Z 1 v (hv0 v)
        simpa using this
      map_smul' := fun a Y => by
        have := hlinY Y 0 a v (hv0 v)
        simpa [h0 v] using this }
  have hsub : ∀ (Y Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : R.smSub),
      R.dC (Y - Z) (v : R.H) = R.dC Y v - R.dC Z v := fun Y Z v => map_sub (f v) Y Z
  have hsm : ∀ (a : ℂ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : R.smSub),
      R.dC (a • Y) (v : R.H) = a • R.dC Y v := fun a Y v => map_smul (f v) a Y
  have hexpP : ∀ (P Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsUnit P →
      (∀ (a b : Fin (2 * r + k + 1)) (v : R.smSub),
        ((E a b v : R.smSub) : R.H) = R.dC (P⁻¹ * Matrix.single a b (1 : ℂ) * P) v) →
      ∀ v : R.smSub, R.dC Y v = ∑ a, ∑ b, (P * Y * P⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
    intro P Y hP hPE v
    calc R.dC Y v = f v Y := rfl
      _ = f v (∑ a, ∑ b, (P * Y * P⁻¹) a b • (P⁻¹ * Matrix.single a b (1 : ℂ) * P)) :=
          congrArg (f v) (conj_expand_units P Y hP)
      _ = ∑ a, ∑ b, (P * Y * P⁻¹) a b • f v (P⁻¹ * Matrix.single a b (1 : ℂ) * P) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul]
      _ = ∑ a, ∑ b, (P * Y * P⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
          simp only [hPE]
          rfl
  have hexp : ∀ (Y : Mx k r) (v : R.smSub),
      R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) :=
    fun Y v => hexpP Q Y hQ hE v
  have hGl : Formalism.REAL.GlRel E := by
    intro a b c d
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hb := hbr (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v (hv0 v)
    rw [conj_units_mul Q hQ, conj_units_mul Q hQ] at hb
    have lhs : (((E a b * E c d - E c d * E a b) v : R.smSub) : R.H) =
        R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (R.dC (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v)
        - R.dC (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) (R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) v) := by
      simp [hE']
    rw [lhs, hb, hsub, hsm, hsm]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, hE']
  refine ⟨hGl, hexp, fun X hX v => ?_⟩
  rw [← hLie X hX v (hv0 v)]
  exact hexp X v

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.MatrixCoefficientDecayStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.matrix_coefficient_decay : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ m : ℕ, ∃ c : ℝ, ∀ a b : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → (∀ Y ∈ b, B.unitLie k r Y) → a.length + b.length ≤ m → ∀ g ∈ GG k r, B.gN g ^ (aOf r h - 1) * ‖⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ‖ ≤ c := by
  first | exact @GlobalTheory.BesselCoefBound.coef_bound | exact GlobalTheory.BesselCoefBound.coef_bound | (intros; apply GlobalTheory.BesselCoefBound.coef_bound <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModel
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quotMeas_ae_mem_and_measurable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hDS hS
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r :=
    Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  have hm : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    simpa [Set.compl_setOf] using this
  have key : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V),
      ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq := by
    intro V _ _ φ hφ
    have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := hφ
    have := hc.aestronglyMeasurable (μ := νq) hm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}) hae] at this
  refine ⟨hae, key, fun a => ?_, fun l hl w hw => ?_⟩
  · exact (key ℝ (fun g => lenA k r z g a) (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable
  · haveI : SecondCountableTopology Wp := by
      haveI : ProperSpace Wp := FiniteDimensional.proper ℂ Wp
      infer_instance
    exact key Wp (fun g => l (R.σ g w))
      (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hDS Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1

end GlobalTheory
end Gp91
end

