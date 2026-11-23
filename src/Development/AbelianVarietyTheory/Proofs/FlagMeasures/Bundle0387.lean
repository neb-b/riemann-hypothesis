module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0313
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0379

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowOfUnimodularLatticePrimitiveVector
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RowsOrb.exists_row_of_unimod : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) → ∃ Λ ∈ Y.what₂ u, ∃ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ = L := by
  intro D large₂ X Y u hStd L hL hU hprim
  obtain ⟨hlat, hun⟩ := GlobalTheory.RowsOrb.Glue.glue_isLattice_unimodular D large₂ X hStd L hL hU
  have hgen := GlobalTheory.RowsOrb.ExGenus.mem_genus_of_isUnimodular D large₂ hStd X u _ hlat hun
  obtain ⟨hx, hx0, hlm, hsub⟩ := GlobalTheory.RowsOrb.parts_of_lat D X u L
  have hzL : GlobalTheory.RowsOrb.zb X u ∈ L := by
    have h1 := (hprim 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rwa [one_smul] at h1
  have hzΛ : X.zu u ∈ latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact ⟨GlobalTheory.RowsOrb.zb X u, hzL, rfl⟩
  have hfix0 := (X.Fu_fixed u).2.2.2.1
  have hlf : (lf D (X.Fu u)) = (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) := by
    show (⟨X.Fu u, (X.Fu u).z⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS _) = _
    rw [X.flagZVector u]
  have hfix : FixedHyp D (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
    refine ⟨hlat, hun, ⟨?_, rfl⟩, ?_, ?_⟩
    · show (X.Fu u).z ∈ _
      rw [X.flagZVector u]; exact hzΛ
    · intro P
      rw [hx]
      rw [← hx0, hlf]
      exact hfix0 P
    · intro c hc
      have hc' : ((c • GlobalTheory.RowsOrb.zb X u : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
        rw [Submodule.coe_smul, GlobalTheory.RowsOrb.zb_coe, ← X.flagZVector u]; exact hc
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((hprim c).1 (hsub _ hc'))
      exact ⟨o, ho⟩
  have hrow : IsRowLat D (X.Fu u) (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := ⟨hgen, hfix, hx⟩
  obtain ⟨Λ', ⟨hΛ', γ, hγ, hmap⟩, -⟩ := (Y.rowsOK u).2 _ hrow
  obtain ⟨g, hg⟩ := GlobalTheory.RowsOrb.exists_gz_lmap D X u γ hγ
  exact ⟨Λ', hΛ', g, by rw [hg, hmap, hlm]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNormsCongrModLevelSq
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormCong

private theorem prime_dvd_int_of_cast_eq_mul {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O}
    (hq : Irreducible q) (hqℓ : q = (ℓ : O)) {m : ℤ} {c : O} (h : (m : O) = q * c) : (ℓ : ℤ) ∣ m := by
  by_contra hnd
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).2 hnd
  apply hq.not_isUnit
  have h1 : ((a * ℓ + b * m : ℤ) : O) = 1 := by rw [hab]; simp
  push_cast at h1
  rw [h, ← hqℓ] at h1
  exact isUnit_iff_exists_inv.2 ⟨a + b * c, by linear_combination h1⟩

theorem int_sq_dvd_of_eq {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O} (hq : Irreducible q)
    (hqℓ : q = (ℓ : O)) {n : ℤ} {c : O} (h : (n : O) = q ^ 2 * c) : (ℓ : ℤ) ^ 2 ∣ n := by
  obtain ⟨m, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ (c := q * c) (by rw [h]; ring)
  push_cast at h
  rw [← hqℓ] at h
  have h2 : ((m : ℤ) : O) = q * c := by
    apply mul_left_cancel₀ hq.ne_zero
    rw [h]; ring
  obtain ⟨k, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ h2
  exact ⟨k, by ring⟩

theorem exists_place_resChar (K : Type) [Field K] [NumberField K] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Formalism.MainNotions.S.Loc.resChar p = ℓ := by
  haveI hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(ℓ : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) _ hker
  have hmem : ((ℓ : ℤ) : 𝓞 K) ∈ Q := by
    have h1 : (ℓ : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (ℓ : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((ℓ : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    exact hℓ.ne_zero (Nat.cast_eq_zero.mp h0)
  refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
  haveI := hQ
  show ringChar (𝓞 K ⧸ Q) = ℓ
  have hz : ((ℓ : ℕ) : 𝓞 K ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    simpa using hmem
  rcases (Nat.dvd_prime hℓ).1 ((ringChar.spec _ ℓ).1 hz) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem sq_dvd_at (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hN : ∀ p, (FP p).NormsOK) (i : Fin 2) :
    ((D.host.g i : ℕ) : ℤ) ^ 2 ∣ (Tn : ℤ) - T'n := by
  obtain ⟨p, hp⟩ := exists_place_resChar D.host.F (D.host.g_prime i)
  have hsome : ((D.s.atP p).split).isSome := by
    rw [D.s_split p, hp]
    fin_cases i <;> simp
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨-, -, -, -, -, hm⟩ := Z.agree p
  rcases hg : (Z.M p).split with _ | g
  · rw [hg, hsg] at hm
    exact (hm : False).elim
  rw [hg, hsg] at hm
  obtain ⟨-, hq⟩ := hm
  obtain ⟨-, -, -, -, hG⟩ := hN p
  obtain ⟨-, c, hc⟩ := hG g hg
  obtain ⟨-, -, hA, hB'⟩ := hB p
  refine int_sq_dvd_of_eq (D.host.g_prime i) g.q_irr ?_ (c := c) ?_
  · apply Subtype.ext
    rw [hq, sg.q_eq, hp]
    simp
  · apply Subtype.ext
    push_cast
    rw [← hA, ← hB']
    exact hc

end GlobalTheory.NormCong

open GlobalTheory.NormCong in
theorem GlobalTheory.NormCong.norms_congr : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).NormsOK) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] := by
  intro D Z FP u u' F F' hB hN
  have h0 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 0
  have h1 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 1
  have hcop : IsCoprime (((D.host.g 0 : ℕ) : ℤ) ^ 2) (((D.host.g 1 : ℕ) : ℤ) ^ 2) := by
    apply IsCoprime.pow
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have h := dvd_sub_comm.1 (hcop.mul_dvd h0 h1)
  rw [Nat.modEq_iff_dvd, show gS D = D.host.g 0 * D.host.g 1 from rfl]
  push_cast
  rw [mul_pow]
  exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairValueInvariantUnitriangularChange
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UniChange

theorem sum_castLE {R : Type} [AddCommMonoid R] {l N : ℕ} (h : l ≤ N) (f : Fin N → R)
    (hf : ∀ c : Fin N, l ≤ c.val → f c = 0) :
    ∑ c, f c = ∑ i : Fin l, f (Fin.castLE h i) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)
  intro c hc
  apply hf
  by_contra hlt
  exact hc ⟨⟨c.val, by omega⟩, rfl⟩

theorem leadMinorE_mul_uni {K : Type} [Field K] {N : ℕ} (L Z A : Matrix (Fin N) (Fin N) K)
    (hL0 : ∀ a b : Fin N, a < b → L a b = 0) (hL1 : ∀ a : Fin N, L a a = 1)
    (hA0 : ∀ a b : Fin N, b < a → A a b = 0) (hA1 : ∀ a : Fin N, A a a = 1) (l : ℕ) :
    leadMinorE (L * Z * A) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · set e := Fin.castLE h with he
    have hsub : (L * Z * A).submatrix e e =
        L.submatrix e e * Z.submatrix e e * A.submatrix e e := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [sum_castLE h]
      · refine Finset.sum_congr rfl (fun d _ => ?_)
        congr 1
        rw [sum_castLE h]
        intro c hc
        rw [hL0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), zero_mul]
      · intro d hd
        rw [hA0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), mul_zero]
    have hLd : (L.submatrix e e).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · exact Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hL1 _)
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        apply hL0
        rw [Fin.lt_def]
        exact (show (i:ℕ) < j from OrderDual.toDual_lt_toDual.mp hij)
    have hAd : (A.submatrix e e).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · exact Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hA1 _)
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        apply hA0
        rw [Fin.lt_def]
        exact (show (j:ℕ) < i from hij)
    rw [hsub, Matrix.det_mul, Matrix.det_mul, hLd, hAd, one_mul, mul_one]
  · rfl

end GlobalTheory.UniChange

open GlobalTheory.UniChange in
theorem GlobalTheory.LocOver.gval_uni_change : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Uni A' → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' → Gval G G' = Gval F F' := by
  intro D T T' F G F' G' A A' hA hA' hZ
  have key : ∀ l, leadMinorE (ZhatL G G') l = leadMinorE (ZhatL F F') l := by
    intro l
    rw [hZ]
    refine leadMinorE_mul_uni _ _ _ ?_ ?_ hA'.1 hA'.2 l
    · intro a b hab
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.1 b a hab]
    · intro a
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.2 a]
  have k1 := key (D.R.rS + 1)
  have k2 := key D.R.rS
  simp only [Gval, Gflag, Dl]
  simp only [ZhatL] at k1 k2
  rw [k1, k2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeaves
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqFam Formalism.MainNotions.S.LocNG GlobalTheory.SnFam

namespace GlobalTheory.SnFam.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem ampQ_not_eq_ampG' {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ Not L = ampG L := by
  funext d
  unfold ampQ ampG
  rw [Finset.sum_eq_single_of_mem ∅ (by simp)]
  · simp
  · intro A hA hne
    simp only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty] at hA
    exact absurd hA.2 hne

private theorem hasPt_of_isPtG {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS)
    (h : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) : HasPt Y u u (Y.tO u u).genSet γ := by
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := h
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa [genT, PB.Terms.ngSet, PB.Terms.genSet] using ht
  · simpa [genT] using hv
  · simpa [NOfG] using hpt

theorem stepFamG_of_fam : (∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) →
    Formalism.L2.SG.FamDefs.HTie → FamGen → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam →
    Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  intro hG6 hH hGen hG5 hW hG4 hE Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH'⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨aF, bF, hF'⟩ := hGen Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW'⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE'⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max aH (max aF (max a5 (max aW (max a4 aE)))),
    max bH (max bF (max b5 (max bW (max b4 bE)))), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin
  simp only [max_le_iff] at hC' hCl
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h4 C' Cl hC'.2.2.2.2.1 hCl.2.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0
    what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin
  refine ⟨s, hs1, hs2, hs3, ?_⟩
  intro γ hγ S
  have hQ := hF' C' Cl hC'.2.1 hCl.2.1 D large₂ X Y u u hc
  have hP := hasPt_of_isPtG Y u (sc s ν) ν (fun _ => 0) γ hγ
  obtain ⟨Fm, hT, hRel, hTerm, hDs, hrw⟩ :=
    hE' C' Cl hC'.2.2.2.2.2 hCl.2.2.2.2.2 D large₂ X Y u u hc _ Not _ _ hQ γ hP
  have h5' : OrbitFamilyIdentityAt Fm Fm.V0 := Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hT (h5 C' Cl hC'.2.2.1 hCl.2.2.1 D large₂ X Y u u hc _ Not _ _ hQ γ hP Fm hT)
  obtain ⟨hWpos, hWle⟩ := hW' C' Cl hC'.2.2.2.1 hCl.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hbk _ Not _ _ hQ γ hP Fm hT hRel hTerm h5'
  have hHt := hH' C' Cl hC'.1 hCl.1 D large₂ X Y u u hc _ _ _ γ Fm hT
  refine ⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S
    (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) (fun L => ampG L) Fm hT hRel hTerm
    hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) h5' ?_ hWpos ?_ ?_⟩
  · simpa [NOfG] using hHt
  · simpa [NOfG] using hWle
  · intro x _
    have h := hs4 _ Not _ _ hQ γ hP Fm hT x.1 x.2
    rw [ampQ_not_eq_ampG'] at h
    rw [← h]
    rfl

end GlobalTheory.SnFam.Gen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalLatticesCountEqProdLocalCountsBadPlaces
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Fibre

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem finrank_eq {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp, rank_eq]

theorem theta_eq_one {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {p : PlF D}
    (h : (FP p).PrimeTo) : LocNG.theta (Z.M p) = 1 := by
  unfold LocNG.theta
  rw [h.1]

theorem isLat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D) (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → t.abelian₂.FG ∧ Submodule.span (D.s.atP p).Ep (t.abelian₂ : Set (Vp D p)) = ⊤ := _root_.GlobalTheory.GenMass.Fibre.termLat

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t := GlobalTheory.T.localTerm_noDefect_primeTo_invariants

theorem full_of_local_span {D : D7} (Z : LocDat D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ) (p : PlF D)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let A := GlobalTheory.HL.placesOf Z
  have hcoord : Submodule.span D.host.E (LatLoc.cL Λ : Set (Fin (nV D) → D.host.E)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hzero⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have := (A.loc p).lf
    have := (A.loc p).char0
    have := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
    let ψ : (Fin (nV D) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (A.loc p).Ep :=
      ∑ i : Fin (nV D), (A.loc p).ιE (φ fun j => if i = j then 1 else 0) • LinearMap.proj i
    have hψ (z : Fin (nV D) → D.host.E) : ψ (A.bc p z) = (A.loc p).ιE (φ z) := by
      rw [φ.pi_apply_eq_sum_univ z, map_sum]
      simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, map_mul, GlobalTheory.HL.Places.bc]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hlat : A.lat p (LatLoc.cL Λ) ≤ (LinearMap.ker ψ).restrictScalars (A.L p).O := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, hz, rfl⟩
      have hz' : φ z ∈ (⊥ : Submodule D.host.E D.host.E) := by
        rw [← hzero]
        exact Submodule.mem_map_of_mem (Submodule.subset_span hz)
      change ψ (A.bc p z) = 0
      rw [hψ, (Submodule.mem_bot D.host.E).mp hz', map_zero]
    have hker : Submodule.span (A.loc p).Ep (A.lat p (LatLoc.cL Λ) : Set _) ≤ LinearMap.ker ψ :=
      Submodule.span_le.mpr hlat
    rw [LatLoc.localLattice_eq] at hspan
    change Submodule.span (A.loc p).Ep (A.lat p (LatLoc.cL Λ) : Set (Fin (nV D) → (A.loc p).Ep)) = ⊤ at hspan
    rw [hspan] at hker
    apply hφ
    apply LinearMap.ext
    intro z
    have hz := LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := A.bc p z)))
    rw [hψ] at hz
    exact (map_eq_zero_iff _ (A.loc p).ιE.injective).mp hz
  refine { toIsLattice := hΛ, span_eq_top := ?_ }
  have hm : (Submodule.span D.host.E (Λ : Set (VS D).V)).map (LatLoc.cE D).toLinearMap = ⊤ := by
    rw [← Submodule.span_image]
    exact hcoord
  apply eq_top_iff.mpr
  intro x _
  have hx : LatLoc.cE D x ∈ (Submodule.span D.host.E (Λ : Set (VS D).V)).map (LatLoc.cE D).toLinearMap := by
    rw [hm]
    exact Submodule.mem_top
  obtain ⟨y, hy, heq⟩ := hx
  have : y = x := (LatLoc.cE D).injective heq
  simpa [this] using hy

theorem fibre : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ y : Dat Z FP, (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) → {p | y p ≠ d0 p}.Finite → ((globSet G G' y).encard : ℝ≥0∞) = ∏ p ∈ P, ((locSet G G' p (y p)).encard : ℝ≥0∞) := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS y hrel hfin
  obtain ⟨hBased, hRelG, hPrime, hTerm0, Λ₀, hΛ₀, hΛ₀t⟩ := hB
  obtain ⟨-, -, -, -, hloc⟩ := hS
  have hLG := LatLoc.lattices_local_global D Z
  haveI : Infinite (PlF D) := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.F
  obtain ⟨p₀, hp₀⟩ : ∃ p : PlF D, p ∉ P := by
    by_contra h
    push_neg at h
    exact Set.infinite_univ (α := PlF D) (P.finite_toSet.subset fun p _ => h p)
  have hΛ₀full : Submodule.IsFullLattice D.host.E Λ₀ :=
    full_of_local_span Z Λ₀ hΛ₀ p₀ (isLat D Z FP p₀ (d0 p₀) _ (hΛ₀t p₀ hp₀)).2

  have single : ∀ p, p ∉ P → ∃! L, L ∈ locSet G G' p (y p) := by
    intro p hp
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have key := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_eq p)
      (hRelG p) (hPrime p hp) A A' (fun a b h => ⟨hA.1 a b h, hA'.1 a b h⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
      (scaled Z p (frame G)) (scaled Z p (frame G'))
      (fun j => by rw [hc j, (hBased p).1]; rfl) (fun j => by rw [hc' j, (hBased p).2.1]; rfl)
      (d0 p) (hTerm0 p) (y p)
    exact key.1 (hrel p hp)

  have std : ∀ p, p ∉ P → y p = d0 p → lattice₂ D Z.M p Λ₀ ∈ locSet G G' p (y p) := by
    intro p hp hy
    rw [hy]
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have hT : LocNG.IsTermOver (FP p) (d0 p) (tm FP G G' p (lattice₂ D Z.M p Λ₀)) :=
      _root_.GlobalTheory.LocOver.WitChange.witness_change (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_eq p) (hRelG p) (d0 p)
        (tm FP F F' p (lattice₂ D Z.M p Λ₀)) (hΛ₀t p hp) A A' (scaled Z p (frame G)) (scaled Z p (frame G')) hA hA'
        (fun a b => ⟨(hint a b).1, (hint a b).2, by
          rw [theta_eq_one (hPrime p hp), map_one]
          refine Submodule.mem_span_singleton.2 ⟨⟨A a b - A' a b, (Z.M p).L.O.sub_mem (hint a b).1 (hint a b).2⟩, ?_⟩
          first
            | (rw [Algebra.smul_def, mul_one]; rfl)
            | (rw [Submodule.smul_def]; simp)
            | (simp [Algebra.smul_def])
            | (erw [smul_eq_mul, mul_one])
            | (change (A a b - A' a b) * 1 = _; rw [mul_one])⟩) hc hc'
    exact ⟨hT, noDefect D Z FP p (hRelG p) (hPrime p hp) (d0 p) _ hT⟩

  let Φ : LV D → ∀ q : P, Submodule (Z.M q).L.O (Vp D q) := fun Λ q => lattice₂ D Z.M q Λ
  have hinj : Set.InjOn Φ (globSet G G' y) := by
    intro Λ₁ h₁ Λ₂ h₂ e
    refine (hLG.1 Λ₁ Λ₂ (full_of_local_span Z Λ₁ h₁.1 p₀ (isLat D Z FP p₀ (y p₀) _ (h₁.2 p₀).1).2) (full_of_local_span Z Λ₂ h₂.1 p₀ (isLat D Z FP p₀ (y p₀) _ (h₂.2 p₀).1).2)).2 fun p => ?_
    by_cases hp : p ∈ P
    · exact congrFun e ⟨p, hp⟩
    · exact (single p hp).unique (h₁.2 p) (h₂.2 p)
  have himg : Φ '' globSet G G' y = Set.univ.pi (fun q : P => locSet G G' q (y q)) := by
    ext g
    constructor
    · rintro ⟨Λ, hΛ, rfl⟩ q -
      exact hΛ.2 q
    · intro hg
      let Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p) := fun p =>
        if h : p ∈ P then g ⟨p, h⟩ else (single p h).exists.choose
      have hLp : ∀ p, Lp p ∈ locSet G G' p (y p) := by
        intro p
        by_cases h : p ∈ P
        · simp only [Lp, dif_pos h]; exact hg ⟨p, h⟩ (Set.mem_univ _)
        · simp only [Lp, dif_neg h]; exact (single p h).exists.choose_spec
      have hlat : ∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤ :=
        fun p => isLat D Z FP p (y p) (tm FP G G' p (Lp p)) (hLp p).1
      have hfin' : {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite := by
        refine ((P.finite_toSet).union hfin).subset fun p hp => ?_
        by_contra hn
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hn
        exact hp ((single p hn.1).unique (hLp p) (std p hn.1 hn.2))
      obtain ⟨Λ, hΛ, hΛp⟩ := hLG.2 Λ₀ hΛ₀full Lp hlat hfin'
      refine ⟨Λ, ⟨hΛ, fun p => by rw [hΛp p]; exact hLp p⟩, ?_⟩
      funext q
      show lattice₂ D Z.M q Λ = g q
      rw [hΛp q]
      show (if h : (q : PlF D) ∈ P then g ⟨q, h⟩ else (single q h).exists.choose) = g q
      rw [dif_pos q.2]
  have e1 := hinj.encard_image
  rw [himg, Set.encard_pi_eq_prod_encard] at e1
  rw [← e1]
  exact (map_prod ENat.toENNRealRingHom (fun i : P => (locSet G G' i (y i)).encard) Finset.univ).trans
    (Finset.prod_coe_sort P (fun p => ((locSet G G' p (y p)).encard : ℝ≥0∞)))

end GlobalTheory.GenMass.Fibre
end
end

