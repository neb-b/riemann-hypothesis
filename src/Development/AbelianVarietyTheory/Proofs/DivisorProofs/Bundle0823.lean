module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0802
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory

theorem rootDiscr_le_of_intermediateField {E : Type} [Field E] [NumberField E]
    (K : IntermediateField ℚ E) : rootDiscr K ≤ rootDiscr E := by
  have hdisc := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) E (𝓞 E)
  have hN : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  have htow := Module.finrank_mul_finrank ℚ K E
  set k := Module.finrank ℚ K
  set m := Module.finrank K E
  have hk : 0 < k := Module.finrank_pos
  have hm : 0 < m := Module.finrank_pos
  have ha : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  have hle : (discr K).natAbs ^ m ≤ (discr E).natAbs := by
    rw [hdisc]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN)
  have hleR : ((discr K).natAbs : ℝ) ^ m ≤ ((discr E).natAbs : ℝ) := by exact_mod_cast hle
  rw [rootDiscr_def, rootDiscr_def, ← htow]
  have e1 : (((|discr K| : ℤ)) : ℝ) = ((discr K).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
  have e2 : (((|discr E| : ℤ)) : ℝ) = ((discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
  rw [e1, e2]
  change _ ^ ((k : ℝ))⁻¹ ≤ _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc ((discr K).natAbs : ℝ) ^ (k : ℝ)⁻¹
      = (((discr K).natAbs : ℝ) ^ m) ^ (((k * m : ℕ) : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        field_simp
    _ ≤ ((discr E).natAbs : ℝ) ^ (((k * m : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (by positivity) hleR (by positivity)

end GlobalTheory

namespace GlobalTheory

theorem abs_lrd_sub_log_d_le_lrd :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
      |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E - Real.log H.d| ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
  intro E _ _ _ H
  have hK := (rootDiscr_and_different_quadField E H).1
  have hle := rootDiscr_le_of_intermediateField (GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.quadField H)
  rw [hK] at hle
  have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.one_lt.le
  have hs : 0 < √(H.d : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hlog0 : 0 ≤ Real.log H.d := Real.log_nonneg hd1
  have hlogs : Real.log √(H.d : ℝ) = Real.log H.d / 2 := by
    rw [Real.log_sqrt (by linarith)]
  have h2 : Real.log H.d / 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
    rw [← hlogs, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd]
    exact Real.log_le_log hs hle
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGenericUnipotentCharacterEqArchMulFinite
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem adele_eq_sInf_add_sFin {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Ad E) :
    x = sInf E (pInf E x) + sFin E (pFin E x) := by
  refine Prod.ext ?_ ?_
  · change x.1 = infEq E ((infEq E).symm x.1) + 0
    simp
  · change x.2 = 0 + x.2
    simp

theorem psiN_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (u : GA E n), GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) * psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
  intro E _ _ _ n u
  have h : GlobalTheory.Whittaker.superDiag u = sInf E (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) + sFin E (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.Whittaker.superDiag, sdM, map_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact adele_eq_sInf_add_sFin _
  unfold GlobalTheory.JSW.psiN psiInf psiFin
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.WhitBump
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleConstantsClosedUnderSizeBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem admissibleConstants_closed_under_sizeBounds : ∀ (𝒞 : FamClass), (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm ∧ DGamSize Fm) →
    Closed 𝒞 (fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm) := by
  intro 𝒞 h𝒞
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  have hK : Nonempty TransportedAlt := ⟨by constructor <;> exact 0⟩
  obtain ⟨K⟩ := hK
  refine ⟨K, fun Fm _ hc _ => ?_⟩
  have hlt : eps < 1 / 52 := lt_of_le_of_lt hle (by norm_num)
  exact _root_.GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize Fm he hlt (h𝒞 Fm hc).1 (h𝒞 Fm hc).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSpecDecomp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.SpecBC

theorem baseChange_specDecomp : ∀ (g a m : ℕ) (O : Type) [CommRing O] (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (χ : Fin a → (O →+* ℂ)) (ω : O) (l l' : ℂ) (E : Fin a → Matrix (Fin g) (Fin g) ℂ), l ≠ l' → (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → (∀ i, E i * E i = E i) → (∀ i, (E i).trace = (m : ℂ)) → (∀ i c, ρ c * E i = χ i c • E i) → (∀ i c, E i * ρ c = χ i c • E i) → (l - l') • ∑ i, E i = ρ ω - l' • (1 : Matrix (Fin g) (Fin g) ℂ) → (∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'), (ρ ω).map j *ᵥ x = j l • x → ∃ y : Fin a → Fin g → R', (∀ i c, (ρ c).map j *ᵥ y i = j (χ i c) • y i) ∧ x = ∑ i, y i) ∧ ∀ (k : Type) [Field k] (j : ℂ →+* k) (i : Fin a), χ i ω = l → Module.finrank k (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) : Submodule k (Fin g → k)) = m := by
  intro g a m O _ ρ χ ω l l' E hll hsep hidem htr hrE hEr hsum
  have hsm : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (r : ℂ) (M : Matrix (Fin g) (Fin g) ℂ),
      (r • M).map j = j r • M.map j := by
    intro R' _ j r M; ext; simp
  have hmul : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (M N : Matrix (Fin g) (Fin g) ℂ),
      (M * N).map j = M.map j * N.map j := by
    intro R' _ j M N; exact Matrix.map_mul

  have hrel : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'),
      j (l - l') • ∑ i, (E i).map j *ᵥ x = (ρ ω).map j *ᵥ x - j l' • x := by
    intro R' _ j x
    have h := congrArg (fun M => (RingHom.mapMatrix j M) *ᵥ x) hsum
    simp only [RingHom.mapMatrix_apply] at h
    have hs : (∑ i, E i).map j = ∑ i, (E i).map j := by ext; simp [Matrix.sum_apply]
    rw [hsm, hs, Matrix.smul_mulVec, Matrix.sum_mulVec] at h
    rw [h, Matrix.map_sub _ (map_sub j), Matrix.sub_mulVec, hsm, Matrix.smul_mulVec, Matrix.map_one _ (map_zero j) (map_one j),
      Matrix.one_mulVec]
  refine ⟨fun R' _ j x hx => ?_, fun k _ j i hi => ?_⟩
  · refine ⟨fun i => (E i).map j *ᵥ x, fun i c => ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    · have hu : IsUnit (j (l - l')) := (sub_ne_zero.mpr hll).isUnit.map j
      have h := hrel R' j x
      rw [hx, ← sub_smul, ← map_sub] at h
      exact (hu.smul_left_cancel.mp h).symm
  · have hj : ∀ z : ℂ, z ≠ 0 → j z ≠ 0 := fun z hz => (hz.isUnit.map j).ne_zero
    have hK : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) :
        Submodule k (Fin g → k)) = LinearMap.range (Matrix.mulVecLin ((E i).map j)) := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range]
      constructor
      · intro hy
        refine ⟨y, ?_⟩
        have hz : ∀ i', i' ≠ i → (E i').map j *ᵥ y = 0 := by
          intro i' hne
          obtain ⟨c, hc⟩ := hsep i' i hne
          have h1 : (E i').map j *ᵥ ((ρ c).map j *ᵥ y) = j (χ i' c) • ((E i').map j *ᵥ y) := by
            rw [Matrix.mulVec_mulVec, ← hmul, hEr, hsm, Matrix.smul_mulVec]
          rw [hy c, Matrix.mulVec_smul] at h1
          have h2 : (j (χ i' c) - j (χ i c)) • ((E i').map j *ᵥ y) = 0 := by
            rw [sub_smul, ← h1, sub_self]
          rw [← map_sub] at h2
          exact (smul_eq_zero.mp h2).resolve_left (hj _ (sub_ne_zero.mpr hc))
        have h := hrel k j y
        rw [hy ω, hi, ← sub_smul, ← map_sub,
          Finset.sum_eq_single i (fun b _ hb => hz b hb) (by simp)] at h
        exact smul_right_injective _ (hj _ (sub_ne_zero.mpr hll)) h
      · rintro ⟨z, rfl⟩ c
        rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    rw [hK]
    have hPP : (E i).map j * (E i).map j = (E i).map j := by rw [← hmul, hidem]
    have he : IsIdempotentElem (Matrix.mulVecLin ((E i).map j)) := by
      unfold IsIdempotentElem
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hPP]
    have h1 := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
    rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin g)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h1
    have htj : ((E i).map j).trace = j (E i).trace := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum]
    rw [htj, htr, map_natCast] at h1
    haveI : CharZero k := (RingHom.charZero_iff j.injective).1 inferInstance
    exact_mod_cast h1.symm

end GlobalTheory.SpecBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.BirigidPow

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem comp_pow_pt {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) : ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

def val {P : LB (G2 A).left} (hP : P.IsLB) {T : Over S} (x y : T ⟶ A) : CechPic.Pic T.left :=
  CechPic.pull (lift x y).left (CechPic.cls P hP)

variable {P : LB (G2 A).left} (hP : P.IsLB)

theorem val_one_left (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) {T : Over S}
    (y : T ⟶ A) : val hP 1 y = 0 := by
  have e : lift (1 : T ⟶ A) y = y ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  rw [val, e, Over.comp_left, CechPic.pull_comp, ← CechPic.cls_pull hP _ (pull_isLB hP _),
    (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 h₁, map_zero]

theorem val_one_right (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) {T : Over S}
    (x : T ⟶ A) : val hP x 1 = 0 := by
  have e : lift x (1 : T ⟶ A) = x ≫ lift (𝟙 A) (1 : A ⟶ A) := by
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  rw [val, e, Over.comp_left, CechPic.pull_comp, ← CechPic.cls_pull hP _ (pull_isLB hP _),
    (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 h₂, map_zero]

theorem add_of_triv {T : Over S} (a b c : T.left ⟶ (G2 A).left)
    (H : ∃ t : (LB.LinComb P (K := Fin 3) ![a, b, c] ![1, -1, -1]).Gen, t.IsGen) :
    CechPic.pull a (CechPic.cls P hP) = CechPic.pull b (CechPic.cls P hP) + CechPic.pull c (CechPic.cls P hP) := by
  have hL := LB.isLB_linComb hP (![a, b, c] : Fin 3 → _) ![1, -1, -1]
  have z := (CechPic.cls_linComb hP _ _ hL).symm.trans ((CechPic.cls_eq_zero_iff hL).2 H)
  rw [Fin.sum_univ_three] at z
  have z' : (1 : ℤ) • CechPic.pull a (CechPic.cls P hP) + (-1 : ℤ) • CechPic.pull b (CechPic.cls P hP) +
      (-1 : ℤ) • CechPic.pull c (CechPic.cls P hP) = 0 := z
  rw [one_zsmul, neg_one_zsmul, neg_one_zsmul] at z'
  rw [← sub_eq_zero, ← z']
  abel

variable (hA : IsAbelianScheme A)
  (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
  (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
  (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)

include hA hamp h₁ h₂

theorem val_mul_left {T : Over S} (x x' y : T ⟶ A) : val hP (x * x') y = val hP x y + val hP x' y :=
  add_of_triv hP _ _ _ (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S A _ hA
    (pull_isLB hP _) hamp P hP h₁ h₂ T x x' y).1

theorem val_mul_right {T : Over S} (x y y' : T ⟶ A) : val hP x (y * y') = val hP x y + val hP x y' :=
  add_of_triv hP _ _ _ (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S A _ hA
    (pull_isLB hP _) hamp P hP h₁ h₂ T y y' x).2

theorem val_pow_left {T : Over S} (x y : T ⟶ A) (n : ℕ) : val hP (x ^ n) y = n • val hP x y := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact val_one_left hP h₁ y
  | succ n ih => rw [pow_succ, val_mul_left hP hA hamp h₁ h₂, ih, succ_nsmul]

theorem val_pow_right {T : Over S} (x y : T ⟶ A) (n : ℕ) : val hP x (y ^ n) = n • val hP x y := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact val_one_right hP h₂ x
  | succ n ih => rw [pow_succ, val_mul_right hP hA hamp h₁ h₂, ih, succ_nsmul]

omit hA hamp h₁ h₂ in
theorem cls_lbPow (m : ℕ) (h : (Hecke.lbPow P m).IsLB) : CechPic.cls _ h = m • CechPic.cls P hP := by
  unfold Hecke.lbPow at h ⊢
  rw [CechPic.cls_linComb hP _ _ h]
  simp [CechPic.pull_id]


include hP in
theorem lineBundleIso_tensorPowSq_pullback_mulPair (n : ℕ) :
    LBIso (Hecke.lbPow P (n ^ 2)) (P.pull (Hecke.sq2 ((𝟙 A) ^ n))) := by
  have hL : (Hecke.lbPow P (n ^ 2)).IsLB := LB.isLB_linComb hP _ _
  refine (CechPic.cls_eq_iff hL (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hP, CechPic.cls_pull hP _ (pull_isLB hP _)]
  change _ = val hP (fst A A ≫ (𝟙 A) ^ n) (snd A A ≫ (𝟙 A) ^ n)
  rw [comp_pow_pt, comp_pow_pt, Category.comp_id, Category.comp_id, val_pow_left hP hA hamp h₁ h₂,
    val_pow_right hP hA hamp h₁ h₂, val, lift_fst_snd, Over.id_left, CechPic.pull_id, smul_smul, sq]


omit hP hA hamp h₁ h₂ in
theorem birigidified_pullback_mulPair_iso_tensorPowSq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) :=
  fun _ _ _ _ hA _ hP h₁ h₂ hamp n => lineBundleIso_tensorPowSq_pullback_mulPair hP hA hamp h₁ h₂ n

end GlobalTheory.BirigidPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
section
noncomputable section

open Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

section Blocks

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

def side (e : ι ≃ Fin a ⊕ Fin b) (i : ι) : Bool := (e i).isRight

def uMat (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : Matrix ι ι K :=
  Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)

theorem uMat_add (e : ι ≃ Fin a ⊕ Fin b) (X Y : Fin a → Fin b → K) :
    uMat e (X + Y) = uMat e X * uMat e Y := by
  simp only [uMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  simp [Matrix.of_add_of, add_comm]

theorem uMat_zero (e : ι ≃ Fin a ⊕ Fin b) : uMat e (0 : Fin a → Fin b → K) = 1 := by
  simp [uMat]

def uGL (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : GL ι K :=
  ⟨uMat e X, uMat e (-X), by rw [← uMat_add, add_neg_cancel, uMat_zero],
    by rw [← uMat_add, neg_add_cancel, uMat_zero]⟩

def uHom (e : ι ≃ Fin a ⊕ Fin b) : Multiplicative (Fin a → Fin b → K) →* GL ι K where
  toFun X := uGL e X.toAdd
  map_one' := Units.ext (uMat_zero e)
  map_mul' X Y := Units.ext (uMat_add e X.toAdd Y.toAdd)

def blockPar (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).BlockTriangular (side e)}
  one_mem' := by simpa using Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa using Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix ι ι K) := Units.invertible g
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def blockParOpp (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i))}
  one_mem' := by simpa using Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa using Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix ι ι K) := Units.invertible g
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def blockLevi (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) := blockPar e ⊓ blockParOpp e

def blockUni (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) := (uHom e).range

end Blocks

section Sums

variable {H : Type} [Group H]

def wt (T L U : Subgroup H) (Ψ : H → ℂ) (x : H) : ℂ :=
  (GlobalTheory.LKLoc.volRat U (GlobalTheory.LKLoc.locPart T L x) : ℂ) * Ψ x

def dsum (T L U : Subgroup H) (Ψ : H → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (T : Set H) (L : Set H), wt T L U Ψ (Quotient.out q)

end Sums

end GlobalTheory.OrbDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMapContinuousMulDetOneCompactSuppo
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory

theorem blockUnipotent_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin N) k), (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → Continuous u ∧ (∀ X Y, u (X + Y) = u X * u Y) ∧ (∀ X, (u X : Matrix (Fin N) (Fin N) k).det = 1) ∧ ∀ f : GL (Fin N) k → ℂ, HasCompactSupport f → ∀ g h : GL (Fin N) k, HasCompactSupport (fun X => f (g * (h⁻¹ * u X * h))) := by
  intro k _ _ _ _ N a b e u hu
  have hmul : ∀ X Y, u (X + Y) = u X * u Y := by
    intro X Y
    ext1
    rw [Units.val_mul, hu, hu, hu]
    simp only [Matrix.reindex_apply, Equiv.symm_symm]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    congr 1
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.of_add_of]
    rw [add_comm X Y]
  have h0 : u 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  have hinv : ∀ X, (u X)⁻¹ = u (-X) := by
    intro X
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← hmul, neg_add_cancel, h0]
  have hentry : ∀ X p q, (u X : Matrix (Fin N) (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)) = X p q := by
    intro X p q
    rw [hu]; simp [Matrix.reindex_apply]
  have hval : Continuous (fun X => (u X : Matrix (Fin N) (Fin N) k)) := by
    have : (fun X => (u X : Matrix (Fin N) (Fin N) k)) = fun X => Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1) := funext hu
    rw [this]
    refine Continuous.matrix_reindex ?_ _ _
    exact Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const
  have hcont : Continuous u := by
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    simp only [hinv]
    exact hval.comp continuous_neg
  refine ⟨hcont, hmul, ?_, ?_⟩
  · intro X
    rw [hu, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    simp
  · intro f hf g h
    set C : Set (GL (Fin N) k) := (fun y => h * (g⁻¹ * y) * h⁻¹) '' tsupport f with hC
    have hCc : IsCompact C := hf.isCompact.image (by fun_prop)
    let E : Fin a → Fin b → GL (Fin N) k → k := fun p q y => (y : Matrix (Fin N) (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q))
    have hE : ∀ p q, Continuous (E p q) := by
      intro p q
      exact (continuous_apply_apply _ _).comp (Units.continuous_val (M := Matrix (Fin N) (Fin N) k))
    refine HasCompactSupport.intro (K := Set.pi Set.univ (fun p => Set.pi Set.univ (fun q => E p q '' C))) ?_ ?_
    · exact isCompact_univ_pi (fun p => isCompact_univ_pi (fun q => hCc.image (hE p q)))
    · intro X hX
      by_contra hne
      apply hX
      have hs : g * (h⁻¹ * u X * h) ∈ tsupport f := subset_tsupport _ hne
      have huC : u X ∈ C := ⟨_, hs, by simp [mul_assoc]⟩
      intro p _ q _
      exact ⟨u X, huC, hentry X p q⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBundleQuotientEquivalence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.KS.Leray

theorem isProper_pow_hom {S : Scheme.{0}} (A : Over S) (hA : IsProper A.hom) (m : ℕ) :
    IsProper (GlobalTheory.KS.pow A m).hom :=
  GlobalTheory.FibrePowerProper.isProper_fan_pt m (fun _ => A) (fun _ => hA) (limit.cone _) (limit.isLimit _)

end GlobalTheory.KS.Leray
end

