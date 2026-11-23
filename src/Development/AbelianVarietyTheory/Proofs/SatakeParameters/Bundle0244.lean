module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicRingEquivEqSelf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

open Topology Filter

theorem adic_ringEquiv_eq_self {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (ψ : w.adicCompletion F ≃+* w.adicCompletion F)
    (hF : ∀ a : F, ψ (algebraMap F _ a) = algebraMap F _ a)
    (hO : ∀ y, y ∈ w.adicCompletionIntegers F ↔ ψ y ∈ w.adicCompletionIntegers F) (y : w.adicCompletion F) :
    ψ y = y := by
  have hval : ∀ b : F, Valued.v (algebraMap F (w.adicCompletion F) b) = w.valuation F b := by
    intro b
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

  have hcmp : ∀ (b : F) (u : w.adicCompletion F), b ≠ 0 →
      (Valued.v u ≤ Valued.v (algebraMap F (w.adicCompletion F) b) ↔
        Valued.v (ψ u) ≤ Valued.v (algebraMap F (w.adicCompletion F) b)) := by
    intro b u hb
    have hb' : (algebraMap F (w.adicCompletion F) b) ≠ 0 := by simpa using hb
    have hpos : 0 < Valued.v (algebraMap F (w.adicCompletion F) b) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb')
    have h1 := hO (u / algebraMap F _ b)
    rw [map_div₀, hF, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, map_div₀, div_le_one₀ hpos,
      div_le_one₀ hpos] at h1
    exact h1

  have hball : ∀ (b : F) (z : w.adicCompletion F), b ≠ 0 →
      {x : w.adicCompletion F | Valued.v (x - z) ≤ Valued.v (algebraMap F (w.adicCompletion F) b)} ∈ 𝓝 z := by
    intro b z hb
    set t := algebraMap F (w.adicCompletion F) b
    have ht : t ≠ 0 := by simpa [t] using hb
    have hpos : 0 < Valued.v t := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht)
    have hc : Continuous fun x : w.adicCompletion F => (x - z) / t := by fun_prop
    have ho := (Valued.isOpen_valuationSubring (w.adicCompletion F)).preimage hc
    refine mem_of_superset (ho.mem_nhds ?_) ?_
    · show (z - z) / t ∈ Valued.v.valuationSubring
      rw [sub_self, zero_div]; exact zero_mem _
    · intro x hx
      have hx' : Valued.v ((x - z) / t) ≤ 1 := hx
      rw [map_div₀, div_le_one₀ hpos] at hx'
      exact hx'
  by_contra hne
  have hz0 : ψ y - y ≠ 0 := sub_ne_zero.mpr hne
  have hvz : Valued.v (ψ y - y) ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuation_surjective F w (Valued.v (ψ y - y) * WithZero.exp (-1 : ℤ))
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hb
    exact (mul_ne_zero hvz WithZero.exp_ne_zero) hb.symm
  have hbv : Valued.v (algebraMap F (w.adicCompletion F) b) < Valued.v (ψ y - y) := by
    rw [hval, hb]
    exact mul_lt_of_lt_one_right (zero_lt_iff.2 hvz) (by have h : (WithZero.exp (1:ℤ))⁻¹ < 1 := compareOfLessAndEq_eq_lt.mp rfl; simpa using h)
  obtain ⟨_, hx, a, rfl⟩ := mem_closure_iff_nhds.1
    ((HeightOneSpectrum.denseRange_algebraMap F w) y) _ (hball b y hb0)
  have h1 : Valued.v (y - algebraMap F _ a) ≤ Valued.v (algebraMap F (w.adicCompletion F) b) := by
    rw [← Valuation.map_neg, neg_sub]; exact hx
  have h2 := (hcmp b _ hb0).1 h1
  rw [map_sub, hF] at h2
  have h3 : ψ y - y = (ψ y - algebraMap F _ a) - (y - algebraMap F _ a) := by ring
  have h4 := Valuation.map_sub Valued.v (ψ y - algebraMap F _ a) (y - algebraMap F _ a)
  rw [← h3] at h4
  exact absurd (h4.trans (max_le h2 h1)) (not_le.2 hbv)

end GlobalTheory.TwV.Xc

namespace GlobalTheory.TwV.Xc

theorem firstFactor_agree : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (W Q : Type) [CommRing W] [Field Q] [Algebra W Q] (w w' : HeightOneSpectrum (𝓞 F)) (e : Q ≃+* w.adicCompletion F) (e' : Q ≃+* w'.adicCompletion F) (φ : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F) (φ' : E ⊗[F] w'.adicCompletion F →+* w'.adicCompletion F), (∀ c, φ ((1 : E) ⊗ₜ[F] c) = c) → (∀ c, φ' ((1 : E) ⊗ₜ[F] c) = c) → (∀ x : Q, x ∈ Set.range (algebraMap W Q) ↔ e x ∈ w.adicCompletionIntegers F) → (∀ x : Q, x ∈ Set.range (algebraMap W Q) ↔ e' x ∈ w'.adicCompletionIntegers F) → (∀ a : E, e.symm (φ (a ⊗ₜ[F] 1)) = e'.symm (φ' (a ⊗ₜ[F] 1))) → w = w' ∧ ∀ x : AfE F E, e.symm (φ (prV (E := E) w x)) = e'.symm (φ' (prV (E := E) w' x)) := by
  intro F E _ _ _ _ _ W Q _ _ _ w w' e e' φ φ' hφ hφ' hW hW' hE
  have hF : ∀ a : F, e.symm (algebraMap F _ a) = e'.symm (algebraMap F _ a) := by
    intro a
    have h := hE (algebraMap F E a)
    have h1 : (algebraMap F E a) ⊗ₜ[F] (1 : w.adicCompletion F) = (1 : E) ⊗ₜ[F] algebraMap F _ a := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    have h2 : (algebraMap F E a) ⊗ₜ[F] (1 : w'.adicCompletion F) = (1 : E) ⊗ₜ[F] algebraMap F _ a := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    rwa [h1, h2, hφ, hφ'] at h
  have hO : ∀ x : Q, e x ∈ w.adicCompletionIntegers F ↔ e' x ∈ w'.adicCompletionIntegers F :=
    fun x => (hW x).symm.trans (hW' x)
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (b : F),
      Valued.v (algebraMap F (v.adicCompletion F) b) = v.valuation F b := by
    intro v b
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hww : w = w' := by
    by_contra hne
    have hle : ¬ w.asIdeal ≤ w'.asIdeal := fun h =>
      hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h))
    obtain ⟨b, hbw, hbw'⟩ := Set.not_subset.1 hle
    have key := hO (e.symm (algebraMap F _ (algebraMap (𝓞 F) F b)⁻¹))
    rw [RingEquiv.apply_symm_apply, hF, RingEquiv.apply_symm_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      hval, hval, map_inv₀, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hbw', inv_one] at key
    have h1 : w.intValuation b < 1 := (HeightOneSpectrum.intValuation_lt_one_iff_mem w b).2 hbw
    have h0 : w.intValuation b ≠ 0 :=
      HeightOneSpectrum.intValuation_ne_zero w b (fun h => hbw' (h ▸ w'.asIdeal.zero_mem))
    have := key.2 le_rfl
    exact absurd this (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 h1))
  subst hww
  refine ⟨rfl, ?_⟩
  have hψ := adic_ringEquiv_eq_self w (e.symm.trans e') (fun a => by simp [hF a])
    (fun y => by simpa using hO (e.symm y))
  have hc : ∀ c, e.symm c = e'.symm c := fun c => by
    have h := hψ c
    simp only [RingEquiv.trans_apply] at h
    rw [← e'.symm_apply_apply (e.symm c), h]
  intro x
  generalize prV (E := E) w x = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
      have : a ⊗ₜ[F] c = (a ⊗ₜ[F] (1 : w.adicCompletion F)) * ((1 : E) ⊗ₜ[F] c) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, map_mul, map_mul, map_mul, map_mul, hφ, hφ', hE a, hc]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockDetResidueCharEqOneOfCongModQ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamQBCong

open GlobalTheory.TopStep

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem entry_cong (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (g : HomE E N N)
    (hg : ∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) (s t : Fin N) :
    IntAt P (g (Pi.single t 1) s) ∧ redP P (g (Pi.single t 1) s) = if s = t then 1 else 0 := by
  classical
  have hq0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hx := mem_stdAt.1 (hg _ (single_mem_stdAt (P := P) t)) s
  set δ : E := (Pi.single t (1 : E) : Sp E N) s with hδ
  have hδI : IntAt P δ := mem_stdAt.1 (single_mem_stdAt (P := P) t) s
  have hdiv : IntAt P ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
    have e : (((qOf P : E)⁻¹ • (g (Pi.single t 1) - Pi.single t 1) : Sp E N)) s = (g (Pi.single t 1) s - δ) / (qOf P : E) := by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [← e]
    exact hx
  have hI : IntAt P (g (Pi.single t 1) s - δ) := by
    have e : g (Pi.single t 1) s - δ = (qOf P : E) * ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
      field_simp
    rw [e]
    exact (intAt_nat _).mul hdiv
  have hI' : IntAt P (g (Pi.single t 1) s) := by
    have := intAt_sub hI (intAt_neg hδI)
    rwa [sub_neg_eq_add, sub_add_cancel] at this
  refine ⟨hI', ?_⟩
  have h0 := redP_eq_zero_of_div hdiv
  rw [reduction_sub hI' hδI, sub_eq_zero] at h0
  rw [h0, hδ, Pi.single_apply]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

theorem lamQB_eq_one_of_cong : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n N : ℕ) (g : HomE E N N), n ≤ N →
    (∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) → LocE.lamQB ξ kj n g = 1 := by
  intro E K _ _ _ _ P ξ kj n N g hn hg
  classical
  unfold LocE.lamQB
  set D : Matrix (Fin (n - kj)) (Fin (n - kj)) E := Matrix.of fun s t : Fin (n - kj) =>
    Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1) with hD
  have hent : ∀ s t : Fin (n - kj), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 E ⧸ P.asIdeal)) s t := by
    intro s t
    have hs : kj + s.1 < N := by have := s.2; omega
    have ht : kj + t.1 < N := by have := t.2; omega
    have e1 : Loc.eN E N (kj + t.1) = Pi.single ⟨kj + t.1, ht⟩ 1 := by
      funext l
      unfold Loc.eN
      rw [Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro h; exact Fin.ext h
      · intro h; rw [h]
    have e2 : D s t = g (Pi.single ⟨kj + t.1, ht⟩ 1) ⟨kj + s.1, hs⟩ := by
      rw [hD, Matrix.of_apply, e1]
      unfold Loc.atN
      rw [dite_eq_left hs]
    obtain ⟨h1, h2⟩ := entry_cong P g hg ⟨kj + s.1, hs⟩ ⟨kj + t.1, ht⟩
    rw [e2]
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.one_apply]
    by_cases hst : s = t
    · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst]
    · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst]
  have hdet : redP P D.det = 1 := by
    rw [(det_int fun s t => (hent s t).1).2]
    have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
    rw [this, Matrix.det_one]
  unfold LocE.unitV
  have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
  rw [this, map_one, Units.val_one, inv_one]

end GlobalTheory.LamQBCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffInLetters
section
noncomputable section

namespace GlobalTheory.LiftTypePrime.ProdComb

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.KernelAt GlobalTheory.ProductJets GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

variable {D : D7} {N N' : ℕ}

theorem mem_stdL {x : Fin N → D.host.E} : x ∈ stdL D N ↔ ∀ k, IsIntegral ℤ (x k) := by
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x k, h⟩, rfl⟩⟩

theorem eqAt_std {p : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : StdAt D p L) : EqAt D p L (stdL D N) := by
  obtain ⟨L₀, h0, h⟩ := h
  rwa [show stdL D N = L₀ from Submodule.ext fun x => mem_stdL.trans (h0 x).symm]

end GlobalTheory.LiftTypePrime.ProdComb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnPrimeToBasePrimePreservesCommonPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU

namespace GlobalTheory.TwU

theorem seamP_under_eq : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok → ∀ P Q : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = Q.under (𝓞 X.F) → (seamP s P).under (𝓞 D.host.F) = (seamP s Q).under (𝓞 D.host.F) := by
  intro D X s hs hX P Q h
  have key : ∀ a : 𝓞 D.host.F, ∃ r : 𝓞 X.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = RingOfIntegers.mapRingEquiv s.iE (algebraMap (𝓞 X.F) (𝓞 X.E) r) := by
    intro a
    set b := (RingOfIntegers.mapRingEquiv s.iE).symm (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) with hb
    have hbe : RingOfIntegers.mapRingEquiv s.iE b = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
      rw [hb, RingEquiv.apply_symm_apply]
    have hfix : X.conjO b = b := by
      apply RingOfIntegers.ext
      apply s.iE.injective
      have h1 : s.iE (b : X.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) :=
        congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hbe
      have h2 : ((X.conjO b : 𝓞 X.E) : X.E) = star (b : X.E) := rfl
      rw [h2, hs.2, h1]
      have h3 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F D.host.E (a : D.host.F) := rfl
      rw [h3, ← Formalism.BasicNotions.Examples₂.star_eq_conj]
      exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
    obtain ⟨r, hr⟩ := GlobalTheory.TwistPlaces.exists_of_conj_eq hX hfix
    exact ⟨r, by rw [hr, hbe]⟩
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
  ext a
  obtain ⟨r, hr⟩ := key a
  have hPQ : r ∈ Ideal.under (𝓞 X.F) P.asIdeal ↔ r ∈ Ideal.under (𝓞 X.F) Q.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, ← HeightOneSpectrum.under_asIdeal, h]
  simp only [Ideal.under, Ideal.mem_comap] at hPQ ⊢
  rw [hr, mem_seamP, mem_seamP]
  exact hPQ

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjExtendPrincipalCongruenceCongOneModQ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.QCong

theorem conj_extE_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (c j D : ℕ) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : GLint E n P), κ ∈ GlobalTheory.TopStep.prinCong n P D → j + 1 ≤ D → (∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ ((qOf P : E) ^ j) • h x ∈ stdAt E (n + c) P) → ∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • ((h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x) ∈ stdAt E (n + c) P := by
  intro E _ _ _ P n c j D h κ hκ hjD hh x hx
  obtain ⟨m, rfl⟩ : ∃ m, D = j + 1 + m := ⟨D - (j + 1), by omega⟩
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hu := (hh x hx).2
  have hw : GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x) ∈ stdAt E n P :=
    GlobalTheory.TopStep.mem_stdAt.2 fun i => GlobalTheory.TopStep.mem_stdAt.1 hu (Fin.castAdd c i)
  have hw' := (GlobalTheory.TopStep.mem_prinCong.1 hκ) _ hw
  have key : (qOf P : E)⁻¹ • (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) = ((qOf P : E) ^ m) • Loc.inX E n c
      ((((qOf P : E) ^ (j + 1 + m))⁻¹) • (κ.1 (GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x)) - GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x))) := by
    rw [GlobalTheory.CongLevel.extE_apply, add_sub_cancel_left, map_smul (GlobalTheory.CongLevel.resX c), map_smul κ.1, ← smul_sub, smul_smul,
      ← map_smul, ← map_smul, smul_smul]
    congr 2
    field_simp
    ring
  have e1 : (h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x = h⁻¹ (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) := by
    rw [map_sub]
    congr 1
    exact (LinearEquiv.symm_apply_apply h x).symm
  rw [e1, ← map_smul, key]
  refine (hh _ ?_).1
  refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
  rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.CongLevel.inX_apply]
  split_ifs with hl
  · exact (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) m).mul (GlobalTheory.TopStep.mem_stdAt.1 hw' _)
  · rw [mul_zero]; exact GlobalTheory.TopStep.intAt_zero

end GlobalTheory.QCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvGLawOfFixedCol
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker MvPolynomial

namespace GlobalTheory.KerJ

theorem ufGL_val {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' γ.1.toLinearMap := by
  simp [ufGL, toGLm]
  rfl

end GlobalTheory.KerJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOneStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  first | (exact @GlobalTheory.DegOneChar.exists_charLift) | (exact GlobalTheory.DegOneChar.exists_charLift) | (intros; apply GlobalTheory.DegOneChar.exists_charLift  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
section
noncomputable section

namespace GlobalTheory.TwV.Xc.Unif

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV
  Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

section OneAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oneAt (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) : AfE F E :=
  Formalism.UG.P.afsplitIE w a + (1 - Formalism.UG.P.afsplitEps E w)

theorem prV_oneAt_self (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) :
    prV (E := E) w (oneAt w a) = a := by
  rw [oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_prV_IE, Formalism.UG.P.afsplit_prV_eps, sub_self, add_zero]

theorem prV_oneAt_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (a : E ⊗[F] w.adicCompletion F) :
    prV (E := E) w' (oneAt w a) = 1 := by
  rw [oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_prV_IE_ne w w' h, Formalism.UG.P.afsplit_prV_eps_ne w w' h,
    sub_zero, zero_add]

theorem ext_prV {x y : AfE F E} (h : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w x = prV (E := E) w y) : x = y := by
  rw [← sub_eq_zero]
  exact Formalism.UG.P.afsplit_inj _ fun w => by rw [map_sub, h, sub_self]

theorem oneAt_mul (w : HeightOneSpectrum (𝓞 F)) (a b : E ⊗[F] w.adicCompletion F) :
    oneAt w a * oneAt w b = oneAt w (a * b) := ext_prV fun w' => by
  by_cases h : w' = w
  · subst h; rw [map_mul, prV_oneAt_self, prV_oneAt_self, prV_oneAt_self]
  · rw [map_mul, prV_oneAt_ne w w' h, prV_oneAt_ne w w' h, prV_oneAt_ne w w' h, one_mul]

theorem oneAt_one (w : HeightOneSpectrum (𝓞 F)) : oneAt (E := E) w 1 = 1 := ext_prV fun w' => by
  by_cases h : w' = w
  · subst h; rw [prV_oneAt_self, map_one]
  · rw [prV_oneAt_ne w w' h, map_one]

theorem sigR_oneAt (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt w a) = oneAt w (sigR σ (w.adicCompletion F) a) := by
  rw [oneAt, oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_sigR_IE, Formalism.UG.P.afsplit_sigR_eps]

def oneAtU (w : HeightOneSpectrum (𝓞 F)) (a : (E ⊗[F] w.adicCompletion F)ˣ) : (AfE F E)ˣ :=
  ⟨oneAt w a, oneAt w (a⁻¹ : (E ⊗[F] w.adicCompletion F)ˣ),
    by rw [oneAt_mul, Units.mul_inv, oneAt_one], by rw [oneAt_mul, Units.inv_mul, oneAt_one]⟩

theorem oneAtU_coe (w : HeightOneSpectrum (𝓞 F)) (a : (E ⊗[F] w.adicCompletion F)ˣ) :
    (oneAtU w a : AfE F E) = oneAt w a := rfl

end OneAt

theorem exists_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime],
    LocGood σ J A → ∀ v, ∃ π ∈ U1 σ, OneOff (A.pl v).1 π ∧ ordA A v π = 1 := by
  intro F E _ _ _ _ _ σ n p G A J _ H v
  have hp0 : (p : (A.pl v).1.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F ((A.pl v).1.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let c : ((A.pl v).1.adicCompletion F × (A.pl v).1.adicCompletion F)ˣ :=
    ⟨((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹),
      ((p : (A.pl v).1.adicCompletion F)⁻¹, (p : (A.pl v).1.adicCompletion F)),
      Prod.ext (mul_inv_cancel₀ hp0) (inv_mul_cancel₀ hp0), Prod.ext (inv_mul_cancel₀ hp0) (mul_inv_cancel₀ hp0)⟩
  let a : (E ⊗[F] (A.pl v).1.adicCompletion F)ˣ := Units.map (A.spl v).symm.toMonoidHom c
  have ha : A.spl v (a : E ⊗[F] (A.pl v).1.adicCompletion F) =
      ((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹) := by
    show A.spl v ((A.spl v).symm _) = _
    rw [RingEquiv.apply_symm_apply]
  refine ⟨oneAtU (A.pl v).1 a, ?_, fun w' hw' => prV_oneAt_ne _ w' hw' _, ?_⟩
  · rw [U1, MonoidHom.mem_ker]
    apply Units.ext
    show oneAt (A.pl v).1 (a : E ⊗[F] (A.pl v).1.adicCompletion F) *
        sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt (A.pl v).1 (a : E ⊗[F] (A.pl v).1.adicCompletion F)) = 1
    rw [sigR_oneAt, oneAt_mul, ← oneAt_one (E := E) (A.pl v).1]
    congr 1
    apply (A.spl v).injective
    rw [map_mul, H.sig v, ha, map_one]
    show (((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹) *
      ((p : (A.pl v).1.adicCompletion F)⁻¹, (p : (A.pl v).1.adicCompletion F)) :
        (A.pl v).1.adicCompletion F × (A.pl v).1.adicCompletion F) = 1
    exact Prod.ext (mul_inv_cancel₀ hp0) (inv_mul_cancel₀ hp0)
  · have := (G.P.setting v).frac_alt
    have hp := (G.P.setting v).p_unif
    have h1 := ordP_eq (Qq := G.P.Qq v) hp 1 1
    have h2 : phiA A v (oneAtU (A.pl v).1 a : AfE F E) = (p : G.P.Qq v) := by
      simp only [phiA, RingHom.comp_apply, oneAtU_coe, prV_oneAt_self]
      show (A.eQ v).symm ((A.spl v (a : E ⊗[F] (A.pl v).1.adicCompletion F)).1) = _
      rw [ha, map_natCast]
    unfold ordA
    rw [h2]
    simpa using h1

end GlobalTheory.TwV.Xc.Unif

end
end

