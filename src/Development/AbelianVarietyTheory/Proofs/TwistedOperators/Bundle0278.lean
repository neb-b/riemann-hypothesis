module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorFaceLevelEqPrincipalLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOpFace

theorem heckeOp_face_to_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (b : Bool) (i : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (B : Finset (GA D (Wc D i))), Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) SF P d B → Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF b i P d B hB
  have hS : OffS D SF P := by
    obtain ⟨_, _, _, _, hS, -⟩ := hB
    exact hS
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.1 SF hSF P).1 hS
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hPP : ∀ L : LevelP R.Pg D.R.r ℂ, ∀ PP, PP ∈ (R.datWp i L).Pg ∨ PP ∈ (R.datWp i L).Q →
      PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := fun L PP h =>
    hG PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  have h1 := ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n)
    (R.datWp i (R.levL F b (sg0 D A))) hβ P hN (hPP _)).2.1 SF d B).1 hB
  exact ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P hN (hPP _)).2.1 SF d B).2 h1

end GlobalTheory.LevOpFace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicUpToFactorOfLoweringKilledTorusWeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol


open GlobalTheory.HolRead in
theorem holUpTo_of_lowKilled : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (la : Wt C.X.Ψ T.rank) (m : D.what₂.Tau → ℤ) (φ : GA D T → ℂ), LowKilled C.θ T B φ → (∀ (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T), φ (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ - la (C.m.e ρ) a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * φ g) → HolUpTo C B la (detPow C.θ T m) φ := by
  intro D S T C B hB la m φ hL htor g
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  obtain ⟨U1, U2, U3⟩ := _root_.GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved D S T C B hB
  obtain ⟨dMul, dNe, dExp⟩ := _root_.GlobalTheory.AdSpan.ConjHol.detPow_mul_ne_zero_exp D C.θ C.inf T m
  let F : Frame C.X.Ψ T.rank → ℂ := fun y =>
    if h : IsUnitFr C.X y then φ (g * (U2 y h).choose) / detPow C.θ T m (U2 y h).choose else 0
  have hF : ∀ a ∈ GinfC T, F (C.xB (C.mvB a B)) = φ (g * a) / detPow C.θ T m a := by
    intro a ha
    have hy := U1 a
    simp only [F, dif_pos hy]
    rw [U3 _ (U2 _ hy).choose_spec.1 a ha (U2 _ hy).choose_spec.2]
  obtain ⟨Q, Q1, Q2⟩ := _root_.GlobalTheory.HolRead.TorusExt.exists_extension _ _ C.X la F (by
    intro y hy t
    obtain ⟨a, ha, rfl⟩ := U2 y hy
    let s : D.what₂.Tau → Fin T.rank → ℝ := fun ρ c => -t (C.m.e ρ) c
    obtain ⟨hk, hk2⟩ := _root_.GlobalTheory.AdSpan.ConjHol.torProd_spec D S T C B hB s
    have e1 := xB_mvB_mul C B hB a (torProd C.θ T B s) (fun τ => diagonal fun c => cexp ((t τ c : ℂ) * I)) fun ρ => ?_
    · erw [← e1]
      rw [hF _ (mul_mem ha hk), hF a ha, ← mul_assoc,
      apply_mul_torProd C.θ T B _ φ htor, apply_mul_torProd C.θ T B _ _ (GlobalTheory.T.realPlaceDeterminantPower_mul_compactTorusElement D S T C B hB m)]
      have hb : (bchar la fun τ => (diagonal fun c => cexp ((t τ c : ℂ) * I) : Matrix (Fin T.rank) (Fin T.rank) ℂ)) =
          cexp (((∑ ρ, ∑ c, ((la (C.m.e ρ) c : ℝ)) * t (C.m.e ρ) c : ℝ) : ℂ) * I) := by
        unfold bchar
        rw [← Equiv.prod_comp C.m.e]
        push_cast
        rw [Finset.sum_mul, Complex.exp_sum]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [Finset.sum_mul, Complex.exp_sum]
        refine Finset.prod_congr rfl fun c _ => ?_
        rw [diagonal_apply_eq, ← Complex.exp_int_mul, mul_assoc]
      have hA : cexp (((∑ ρ, ∑ c, ((m ρ - la (C.m.e ρ) c : ℤ) : ℝ) * s ρ c : ℝ) : ℂ) * I) =
          cexp (((∑ ρ, ∑ c, ((m ρ : ℤ) : ℝ) * s ρ c : ℝ) : ℂ) * I) *
            cexp (((∑ ρ, ∑ c, ((la (C.m.e ρ) c : ℝ)) * t (C.m.e ρ) c : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add, ← add_mul]
        congr 2
        rw [← Complex.ofReal_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [s]; push_cast; ring
      rw [hb, hA]
      field_simp [dNe a, Complex.exp_ne_zero]
      <;> ring
    · rw [hk2]
      show _ = B ρ * (diagonal fun c => cexp ((t (C.m.e ρ) c : ℂ) * I)).map (starRingEnd ℂ) * (B ρ)⁻¹
      rw [diagonal_map (map_zero _)]
      congr 3
      funext c
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      simp only [s]; push_cast; ring_nf)
  have hQ : ∀ a ∈ GinfC T, Q (C.xB (C.mvB a B)) = φ (g * a) / detPow C.θ T m a := fun a ha => by
    rw [Q1 _ (U1 a), hF a ha]
  refine ⟨Q, GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative _ _ C.X la Q Q2 fun y hy => ?_, Q2, fun a ha => ?_⟩
  swap
  · rw [hQ a ha]; field_simp [dNe a]
  obtain ⟨a, ha, rfl⟩ := U2 y hy
  have hs : DifferentiableAt ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 :=
    (((GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hL.1) (g * a)).differentiable
      (by simp)) 0
  let L : Frame C.X.Ψ T.rank →L[ℝ] GlobalTheory.SmoothForms.LieN T := LinearMap.toContinuousLinearMap (toLieC C R B)
  let lam : GlobalTheory.SmoothForms.LieN T →L[ℝ] ℂ :=
    { toLinearMap := trLin T m
      cont := by
        change Continuous (fun Y : GlobalTheory.SmoothForms.LieN T => ∑ ρ, (m ρ : ℂ) * trace (Y ρ).1)
        fun_prop }
  let f : GlobalTheory.SmoothForms.LieN T → ℂ := fun Y =>
    (detPow C.θ T m a)⁻¹ * (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y) * cexp (-lam Y))
  have key : ∀ Z ∈ unitLie C.X, Q (rmul (C.xB (C.mvB a B)) (expFr Z)) = f (L Z) := by
    intro Z hZ
    have he := GlobalTheory.SmoothForms.isExpFam_expInf R (L Z)
    rw [← xB_mvB_mul C B hB a _ _ fun ρ => ?_, hQ _ (mul_mem ha he.1), dMul, dExp]
    · simp only [f, lam, mul_assoc, Complex.exp_neg]
      field_simp [dNe a]
      rfl
    · show infMat _ _ (C.θ ρ) _ = _
      rw [he.2 ρ]
      change NormedSpace.exp ((toLieC C R B Z ρ).1) = _
      rw [(_root_.GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec D S T C R B hB Z hZ).1 ρ,
        Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det _).2 (isUnit_det_B C hB ρ))]
      congr 2
      exact (exp_map_conj _).symm
  have h0 : (0 : Frame C.X.Ψ T.rank) ∈ unitLie C.X := fun τ => by
    have : mat (0 : Frame C.X.Ψ T.rank) τ = 0 := rfl
    simp [this]
  let Dφ := fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0
  have hE : HasFDerivAt (fun Y : GlobalTheory.SmoothForms.LieN T => cexp (-lam Y)) (cexp (-lam 0) • -lam) 0 :=
    lam.hasFDerivAt.neg.cexp
  have hfd := (hs.hasFDerivAt.mul hE).const_mul (detPow C.θ T m a)⁻¹
  have hfd' : HasFDerivAt f ((detPow C.θ T m a)⁻¹ • (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) •
      (cexp (-lam 0) • -lam) + cexp (-lam 0) • Dφ)) (L 0) := by
    have h0L : L 0 = 0 := map_zero L
    rw [h0L]; exact hfd
  refine ⟨_ , (hfd'.comp (0 : Frame C.X.Ψ T.rank) L.hasFDerivAt).hasFDerivWithinAt.congr key (key 0 h0), ?_⟩
  intro τ c d hcd Z hZ Z' hZ' e
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective τ
  have hD := _root_.GlobalTheory.AdSpan.ConjHol.fderiv_toLieC_eq_zero D S T C R B hB φ hL (g * a) ρ c d hcd Z Z' hZ hZ' e
  have hT := _root_.GlobalTheory.AdSpan.ConjHol.trLin_toLieC_unitFr D S T C R B hB m ρ c d hcd Z Z' hZ hZ' e
  have hℓ : ∀ W : Frame C.X.Ψ T.rank, ((detPow C.θ T m a)⁻¹ • (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) •
      (cexp (-lam 0) • -lam) + cexp (-lam 0) • Dφ)).comp L W = (detPow C.θ T m a)⁻¹ *
      (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) * (cexp (-lam 0) * -trLin T m (toLieC C R B W)) +
        cexp (-lam 0) * Dφ (toLieC C R B W)) := by
    intro W
    simp [L, lam, ContinuousLinearMap.comp_apply, mul_assoc]
    <;> ring
  rw [hℓ, hℓ]
  linear_combination ((detPow C.θ T m a)⁻¹ * cexp (-lam 0)) * hD -
    ((detPow C.θ T m a)⁻¹ * φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) * cexp (-lam 0)) * hT

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrAct


open Classical in
noncomputable def partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) : GA D V :=
  ofInf D.sp.cm.sig V.gram (embArchPi D.sp.cm.sig V.gram fun w =>
    if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1)

open Classical in
theorem projArch_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (w : InfinitePlace D.host.F) :
    projArch D.sp.cm.sig V.gram w (partAt V g s) =
      if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1 := by
  rw [partAt, projArch_ofInf, projInfArch_embArchPi]

theorem proj_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    proj D.sp.cm.sig V.gram v (partAt V g s) = 1 := by
  rw [partAt, proj_ofInf]

open Classical in
theorem partAt_insert {D : D7} (V : HSp D) (g : GA D V) {s : Finset D.what₂.Tau} {τ : D.what₂.Tau} (hτ : τ ∉ s) :
    partAt V g (insert τ s) =
      embW V (placeOf D τ) (projArch D.sp.cm.sig V.gram (placeOf D τ) g) * partAt V g s := by
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [map_mul, projArch_partAt, projArch_partAt]
    by_cases hw : w = placeOf D τ
    · subst hw
      have h1 : placeOf D τ ∈ (insert τ s).image (placeOf D) := Finset.mem_image_of_mem _ (Finset.mem_insert_self τ s)
      have h2 : placeOf D τ ∉ s.image (placeOf D) := fun h => by
        obtain ⟨ρ, hρ, e⟩ := Finset.mem_image.1 h
        exact hτ ((placeOf_bijective D).1 e ▸ hρ)
      rw [if_pos h1, if_neg h2, mul_one]
      exact (projArch_embArch_self _ _ _ _).symm
    · rw [projArch_embArch_ne _ _ hw, one_mul]
      congr 1
      simp only [Finset.image_insert, Finset.mem_insert, hw, false_or]
  · rw [map_mul, proj_partAt, proj_partAt, proj_embArch, one_mul]

theorem partAt_univ {D : D7} (V : HSp D) (g : GA D V) [Fintype D.what₂.Tau] :
    partAt V g Finset.univ = (toInf V g : GA D V) := by
  classical
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [projArch_partAt, if_pos]
    · show _ = projArch D.sp.cm.sig V.gram w (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
      rw [projArch_ofInf, projInfArch_projInf]
    · obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
      exact Finset.mem_image_of_mem _ (Finset.mem_univ τ)
  · rw [proj_partAt]
    show _ = proj D.sp.cm.sig V.gram v (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
    rw [proj_ofInf]

end GlobalTheory.TrAct


open GlobalTheory.TrAct in
theorem GlobalTheory.TrAct.toInf_apply_homDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H), ∀ Φ ∈ homDS M ρ U, ∀ (g : GA D V) y, ρ (toInf V g : GA D V) (Φ y) = Φ fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  intro D V S M H _ _ _ ρ U Φ hΦ g y
  classical
  haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
  haveI : Fintype D.what₂.Tau := Fintype.ofFinite _
  have key : ∀ s : Finset D.what₂.Tau, ρ (partAt V g s) (Φ y) = Φ fun τ =>
      if τ ∈ s then dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) else y τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : partAt V g ∅ = 1 := by
        rw [partAt]
        have : (fun w => if w ∈ (∅ : Finset D.what₂.Tau).image (placeOf D) then
            projArch D.sp.cm.sig V.gram w g else (1 : GArch D.sp.cm.sig V.gram w)) = 1 := by
          funext w; simp
        rw [this, map_one, map_one]
      simp [this]
    | insert τ s hτ ih =>
      rw [partAt_insert V g hτ, map_mul, ContinuousLinearMap.mul_apply, ih, ← (mem_homPi.1 hΦ).2 τ]
      congr 1
      funext τ'
      by_cases e : τ' = τ
      · subst e
        simp [hτ]
      · rw [Function.update_of_ne e]
        simp [e]
  have := key Finset.univ
  rw [partAt_univ] at this
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemClosureSpan
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
open scoped InnerProductSpace

namespace GlobalTheory.TensorTrace

section Hilbert

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_eq_zero_of_mem_closure_span {S : Set H} {a : H} (h : ∀ x ∈ S, ⟪x, a⟫_ℂ = 0)
    {x : H} (hx : x ∈ (Submodule.span ℂ S).topologicalClosure) : ⟪x, a⟫_ℂ = 0 := by
  have hle : (Submodule.span ℂ S).topologicalClosure ≤ (ℂ ∙ a)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    intro y hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h y hy)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hx)

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_orthonormal (L : W →ₗ[ℂ] H) (hL : Function.Injective L) (Z : Submodule ℂ W)
    [FiniteDimensional ℂ Z] :
    ∃ (n : ℕ) (z : Fin n → W), (∀ j, z j ∈ Z) ∧ Orthonormal ℂ (fun j => L (z j)) ∧
      (∀ x ∈ Z, L x = ∑ j, ⟪L (z j), L x⟫_ℂ • L (z j)) ∧
      (∀ (f : W →ₗ[ℂ] W) (hf : ∀ x ∈ Z, f x ∈ Z),
        LinearMap.trace ℂ Z (f.restrict hf) = ∑ j, ⟪L (z j), L (f (z j))⟫_ℂ) := by
  let LZ := L ∘ₗ Z.subtype
  have hLZ : Function.Injective LZ := hL.comp Subtype.val_injective
  let e := LinearEquiv.ofInjective LZ hLZ
  haveI : FiniteDimensional ℂ (LinearMap.range LZ) := LinearEquiv.finiteDimensional e
  let b := stdOrthonormalBasis ℂ (LinearMap.range LZ)
  have he : ∀ x : Z, ((e x : LinearMap.range LZ) : H) = L x := fun x => rfl
  have hb : ∀ j, L ((e.symm (b j) : Z) : W) = (b j : H) := fun j => by
    rw [← he, e.apply_symm_apply]
  refine ⟨_, fun j => ((e.symm (b j) : Z) : W), fun j => (e.symm (b j)).2, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro j k
    simp only [hb]
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.1 b.orthonormal j k
  · intro x hx
    have h1 := congrArg (fun v : LinearMap.range LZ => (v : H)) (b.sum_repr' (e ⟨x, hx⟩))
    simp only [Submodule.coe_sum, Submodule.coe_smul, he] at h1
    simp only [hb]
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, he]
  · intro f hf
    rw [← LinearMap.trace_conj' _ e, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, hb, LinearEquiv.conj_apply]
    rfl

end Hilbert

section Tensor

variable {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
  [∀ i, InnerProductSpace ℂ (Hs i)] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evalAt (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (u : ∀ i, Hs i) : W →ₗ[ℂ] H where
  toFun w := T w u
  map_add' a b := by simp
  map_smul' c a := by simp

theorem evalAt_apply (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (u : ∀ i, Hs i) (w : W) :
    evalAt T u w = T w u := rfl

variable {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H} {β : W → W → ℂ}

theorem beta_eq (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {u : ∀ i, Hs i} (hu : ∀ i, ⟪u i, u i⟫_ℂ = 1) (w w' : W) :
    β w w' = ⟪evalAt T u w', evalAt T u w⟫_ℂ := by
  rw [evalAt_apply, evalAt_apply, hβ]
  simp only [hu, Finset.prod_const_one, mul_one]

theorem evalAt_injective (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {u : ∀ i, Hs i} (hu : ∀ i, ⟪u i, u i⟫_ℂ = 1) (hT : Function.Injective T) :
    Function.Injective (evalAt T u) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => hT ?_
  rw [map_zero]
  ext y
  have h1 : β w w = 0 := by rw [beta_eq hβ hu, hw, inner_zero_left]
  have h2 : ⟪T w y, T w y⟫_ℂ = 0 := by rw [hβ, h1, zero_mul]
  simpa using inner_self_eq_zero.1 h2

variable [CompleteSpace H]

theorem starProjection_tensor
    (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {z : W} (hz : β z z = 1) (w : W) (y : ∀ i, Hs i) :
    (Submodule.span ℂ {x | ∃ y', x = T z y'}).topologicalClosure.starProjection (T w y) = β w z • T z y := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun x hx => ?_
  · exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩))
  · rw [inner_eq_zero_symm]
    refine inner_eq_zero_of_mem_closure_span ?_ hx
    rintro _ ⟨y', rfl⟩
    rw [inner_sub_right, inner_smul_right, hβ, hβ, hz, one_mul, sub_self]

theorem starProjection_eq_zero_tensor {z : W} {v : H} (hv : ∀ y, ⟪T z y, v⟫_ℂ = 0) :
    (Submodule.span ℂ {x | ∃ y', x = T z y'}).topologicalClosure.starProjection v = 0 := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) fun x hx => ?_
  rw [sub_zero, inner_eq_zero_symm]
  exact inner_eq_zero_of_mem_closure_span (by rintro _ ⟨y, rfl⟩; exact hv y) hx

end Tensor

theorem hasTrace_finiteRank_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Type) [AddCommGroup W] [Module ℂ W] (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (β : W → W → ℂ), (∀ w w' y y', inner ℂ (T w' y') (T w y) = β w w' * ∏ i, inner ℂ (y' i) (y i)) → Function.Injective T → (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = ⊤ → ∀ (A : W →ₗ[ℂ] W) (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A c → ∀ Z : Submodule ℂ W, FiniteDimensional ℂ Z → LinearMap.range A ≤ Z → (∀ w, (∀ z ∈ Z, β w z = 0) → A w = 0) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ w y, X (T w y) = T (A w) fun i => B i (y i)) → HasTrace X (c * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ W _ _ T β hβ hT hdense A c hA Z _ hAZ hA0 B b hB X hX
  by_cases hnt : ∀ i, Nontrivial (Hs i)
  · obtain ⟨u, hu⟩ : ∃ u : ∀ i, Hs i, ∀ i, ⟪u i, u i⟫_ℂ = 1 := by
      have hv : ∀ i, ∃ v : Hs i, v ≠ 0 := fun i => @exists_ne _ (hnt i) 0
      choose v hv using hv
      refine ⟨fun i => ((‖v i‖ : ℂ)⁻¹) • v i, fun i => ?_⟩
      rw [inner_self_eq_norm_sq_to_K, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 (hv i))]
      simp
    obtain ⟨n, z, hzZ, hon, hdec, htr⟩ :=
      exists_orthonormal (evalAt T u) (evalAt_injective hβ hu hT) Z
    have hzz : ∀ j, β (z j) (z j) = 1 := fun j => by
      have := orthonormal_iff_ite.1 hon j j
      simp only [if_pos rfl] at this
      rw [beta_eq hβ hu]
      exact this
    have hAw : ∀ w, A w = ∑ j, β w (z j) • A (z j) := by
      intro w
      have hperp : ∀ k, ⟪evalAt T u (z k), evalAt T u (w - ∑ j, β w (z j) • z j)⟫_ℂ = 0 := by
        intro k
        have h1 := hon.inner_right_fintype (fun j => β w (z j)) k
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum, inner_sub_right]
        simp only [map_smul]
        rw [h1, beta_eq hβ hu, sub_self]
      have h0 : A (w - ∑ j, β w (z j) • z j) = 0 := by
        refine hA0 _ fun x hx => ?_
        rw [beta_eq hβ hu, hdec x hx, sum_inner]
        exact Finset.sum_eq_zero fun k _ => by rw [inner_smul_left, hperp k, mul_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero] at h0
      simpa only [map_smul] using h0
    let P : Fin n → H →L[ℂ] H := fun j =>
      (Submodule.span ℂ {x | ∃ y', x = T (z j) y'}).topologicalClosure.starProjection
    have hXsum : X = ∑ j, X ∘L P j := by
      refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 hdense) ?_
      rintro _ ⟨w, y, rfl⟩
      rw [ContinuousLinearMap.sum_apply]
      simp only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz _), map_smul, hX]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hAw w, map_sum, ContinuousMultilinearMap.sum_apply]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply]
    have hj : ∀ j, GlobalTheory.OpTrace.HasTrace (X ∘L P j) (β (A (z j)) (z j) * ∏ i, b i) := fun j =>
      _root_.GlobalTheory.tensorTrace_hasTrace ι Hs H (T (z j)) (T (A (z j))) (β (A (z j)) (z j)) (β (A (z j)) (A (z j)))
        (fun y y' => by rw [hβ, hzz, one_mul]) (fun y y' => hβ _ _ _ _) (fun y y' => hβ _ _ _ _) B b hB
        (X ∘L P j)
        (fun y => by
          simp only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz j), hzz j, one_smul, hX])
        (fun v hv => by
          simp only [ContinuousLinearMap.comp_apply, P, starProjection_eq_zero_tensor hv, map_zero])
    have hf : ∀ x ∈ Z, A x ∈ Z := fun x _ => hAZ (LinearMap.mem_range_self A x)
    have hc : c = ∑ j, β (A (z j)) (z j) := by
      have h1 := GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le W A Z hAZ
      rw [← hA.2, h1.2, htr A hf]
      simp only [beta_eq hβ hu]
    rw [hXsum]
    refine ⟨GlobalTheory.OpTrace.isTraceClass_sum _ fun j _ => (hj j).1, ?_⟩
    rw [GlobalTheory.OpTrace.trace_sum _ fun j _ => (hj j).1, hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => (hj j).2
  · push_neg at hnt
    obtain ⟨i0, hi0⟩ := hnt
    have hTz : ∀ w y, T w y = 0 := fun w y => (T w).map_coord_zero i0 (Subsingleton.elim _ _)
    have hH : ∀ v : H, v = 0 := by
      intro v
      have hv : v ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure := by
        rw [hdense]; exact Submodule.mem_top
      have := inner_eq_zero_of_mem_closure_span (a := v)
        (by rintro _ ⟨w, y, rfl⟩; rw [hTz, inner_zero_left]) hv
      exact inner_self_eq_zero.1 this
    have hX0 : X = 0 := ContinuousLinearMap.ext fun v => hH _
    have hB0 : B i0 = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
    have hb0 : b i0 = 0 := by rw [← (hB i0).2, hB0, GlobalTheory.OpTrace.trace_zero]
    rw [hX0, Finset.prod_eq_zero (Finset.mem_univ i0) hb0, mul_zero]
    exact ⟨GlobalTheory.OpTrace.isTraceClass_zero, GlobalTheory.OpTrace.trace_zero⟩

end GlobalTheory.TensorTrace
end
end

