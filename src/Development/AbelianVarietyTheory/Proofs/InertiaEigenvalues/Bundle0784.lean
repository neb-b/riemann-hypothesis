module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open Classical
namespace GlobalTheory.ExportSeries
open GlobalTheory.PlaceModel

variable {D : D7}

theorem isPlaceModel_restrictHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ha : a' * a' = a') (hb : b * b = b)
    (hab : a' * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := _root_.GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf ha hb hab hΛ hT

theorem toEAf_mem_intAf_of_idem {e : AE D} (he : e * e = e) : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := _root_.GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem he

theorem isIntM_of_mem_lat_half {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    {x : WO S T} (hx : IsHalf (idem R) x) (hl : x ∈ F.lat) :
    IsIntM (frMapO S T F.βS F.βT x) ∧ IsIntM (frMapAdj S T F.βS F.βT x) :=
  _root_.GlobalTheory.LatHalfInt.frMap_int_of_mem_lat hF hR hx hl

theorem mem_lat_of_isIntM_half {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    {x : WO S T} (hx : IsHalf (idem R) x) (hi : IsIntM (frMapO S T F.βS F.βT x)) : x ∈ F.lat := _root_.GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int hF hR hx hi

theorem redM_halfIdem_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Pg Qa Qb : Finset (Pl D.host.E)} (hP : PlacesOK Pg Qa) (hQ : Qb ⊆ Qa) {x : WO S T}
    (hx : IsHalf (halfIdem Pg Qa) x) (h1 : IsIntM (frMapAdj S T βS βT x)) (h2 : IsIntM (frMapO S T βS βT x)) :
    (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧
    (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) :=
  _root_.GlobalTheory.RedHalfDrop.redM_drop βS βT hP hQ hx h1 h2

end GlobalTheory.ExportSeries

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open Classical
namespace GlobalTheory.ExportSeries
open GlobalTheory.PlaceModel GlobalTheory.AdelicLatMove

variable {D : D7}

theorem halfIdem_eq_add {Pg Qa Qb : Finset (Pl D.host.E)} (hQ : Qb ⊆ Qa) :
    halfIdem Pg Qa = halfIdem Pg Qb + idem (Qa \ Qb) := by
  unfold halfIdem idem
  rw [← Finset.sum_sdiff hQ]
  ring

theorem PlacesOK.empty_sdiff {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa) : PlacesOK ∅ (Qa \ Qb) :=
  ⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, Finset.sdiff_subset.trans hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _,
    fun PP hPP => h.prime PP (Or.inr (Finset.sdiff_subset (hPP.resolve_left (Finset.notMem_empty PP))))⟩

theorem idem_mul_self_of {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) : idem R * idem R = idem R := by
  have := h.isOrthSum.1.idem
  rwa [halfIdem, idem_empty, map_zero, zero_add] at this

theorem halfIdem_mul_idem {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa) (hQ : Qb ⊆ Qa) :
    halfIdem Pg Qb * idem (Qa \ Qb) = 0 := by
  have h1 := h.isOrthSum.1.idem
  have h2 := (h.mono hQ).isOrthSum.1.idem
  have h3 := idem_mul_self_of (h.empty_sdiff (Qb := Qb))
  rw [halfIdem_eq_add hQ] at h1
  refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
  push_cast
  linear_combination h1 - h2 - h3

theorem frMapO_add' {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (e • x) = toEAf D (cA D e) • frMapAdj S T βS βT x := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]
  have : (((e • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D e) • ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem isIntM_smul {b a : ℕ} {e : AE D} (he : e * e = e) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    IsIntM (toEAf D e • N) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem (toEAf_mem_intAf_of_idem he) (hN i j)

theorem isIntM_smul_cA {b a : ℕ} {e : AE D} (he : e * e = e) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    IsIntM (toEAf D (cA D e) • N) := isIntM_smul (by rw [← map_mul, he]) hN

theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (x : Mx D m n) : IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, he]

theorem isInt_iff {S T : HSp D} {F : Frame S T} (hF : F.Good) {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa)
    (hQ : Qb ⊆ Qa) {x : WO S T} (hx : IsHalf (halfIdem Pg Qa) x) :
    (IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) ↔
      (IsIntM (frMapAdj S T F.βS F.βT (halfIdem Pg Qb • x)) ∧ IsIntM (frMapO S T F.βS F.βT (halfIdem Pg Qb • x)) ∧
        idem (Qa \ Qb) • x ∈ F.lat) := by
  have hR := h.empty_sdiff (Qb := Qb)
  have ha' := (h.mono hQ).isOrthSum.1.idem
  have hb := idem_mul_self_of hR
  have hxe : x = halfIdem Pg Qb • x + idem (Qa \ Qb) • x := by
    rw [← add_smul, ← halfIdem_eq_add hQ]
    exact (Matrix.ext fun i j => hx i j).symm
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, mem_lat_of_isIntM_half hF hR (isHalf_smul hb x) ?_⟩
    · rw [frMapAdj_smul]; exact isIntM_smul_cA ha' h1
    · rw [frMapO_smul]; exact isIntM_smul ha' h2
    · rw [frMapO_smul]; exact isIntM_smul hb h2
  · rintro ⟨k1, k2, k3⟩
    obtain ⟨o, d⟩ := isIntM_of_mem_lat_half hF hR (isHalf_smul hb x) k3
    rw [hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add']
    exact ⟨fun i j => add_mem (k1 i j) (d i j), fun i j => add_mem (k2 i j) (o i j)⟩

theorem datumFn_eq_restrict {S T : HSp D} {F : Frame S T} (hF : F.Good) {G : TypeDat D T.rank}
    {Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK G.Pg Qa) (hQ : Qb ⊆ Qa) {ω : Reds D T.rank S.rank → ℂ}
    (hω : ∀ y y', (∀ PP ∈ Qb, y PP = y' PP) → ω y = ω y') :
    F.datumFn G Qa ω = restrictHalf (halfIdem G.Pg Qb) (idem (Qa \ Qb)) F.lat (F.datumFn G Qb ω) := by
  funext x
  have ha' := (h.mono hQ).isOrthSum.1.idem
  have hb := idem_mul_self_of (h.empty_sdiff (Qb := Qb))
  rw [restrictHalf_apply, ← halfIdem_eq_add hQ]
  by_cases hx : IsHalf (halfIdem G.Pg Qa) x
  swap
  · rw [if_neg hx, mul_zero]
    simp only [Frame.datumFn]
    rw [if_neg fun h => hx h.1, zero_mul]
  rw [if_pos hx, mul_one]
  have ha'x := isHalf_smul ha' x
  have hbx := isHalf_smul hb x
  by_cases hint : IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)
  · obtain ⟨k1, k2, k3⟩ := (isInt_iff hF h hQ hx).1 hint
    obtain ⟨r1, r2⟩ := redM_halfIdem_smul F.βS F.βT h hQ hx hint.1 hint.2
    simp only [Frame.datumFn, halfInd]
    rw [if_pos ⟨hx, hint.1⟩, if_pos ⟨hx, hint.2⟩, if_pos ⟨ha'x, k1⟩, if_pos ⟨ha'x, k2⟩, if_pos ⟨k3, hbx⟩, mul_one]
    congr 1
    · exact GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hPP => r1 PP hPP
    · exact hω _ _ fun PP hPP => r2 PP hPP
  · have hL : F.datumFn G Qa ω x = 0 := by
      rcases not_and_or.1 hint with h1 | h1
      · simp [Frame.datumFn, h1]
      · simp [Frame.datumFn, h1]
    rw [hL]
    have hr := mt (isInt_iff hF h hQ hx).2 hint
    rcases not_and_or.1 hr with h1 | h1
    · simp [Frame.datumFn, h1]
    rcases not_and_or.1 h1 with h1 | h1
    · simp [Frame.datumFn, h1]
    · simp [halfInd, h1]

theorem vecAt_drop : ∀ (D : D7) (S T : HSp D) (B : Base S T) (Q Q' : Finset (Pl D.host.E)) [DecidablePred (· ∈ Q')]
    (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ), B.Good → B.admitted Q → Q' ⊆ Q →
    B.vecAt Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.vecAt Q' fun PP => φ PP.1 := by
  intro D S T B Q Q' _ φ hB hQ hQ'
  classical
  have hL : B.locFn Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.locFn Q' (fun PP => φ PP.1) := by
    funext y
    unfold Base.locFn
    congr 1
    beta_reduce
    rw [Finset.prod_coe_sort Q (fun P => if P ∈ Q' then φ P (y P) else 1),
      ← Finset.prod_subset hQ' (fun P _ hn => if_neg hn), Finset.prod_coe_sort Q' (fun P => φ P (y P))]
    exact Finset.prod_congr rfl fun P hP => if_pos hP
  have hQb : B.de.Q ∪ Q' ⊆ B.de.Q ∪ Q := Finset.union_subset_union (subset_refl _) hQ'
  have hω : ∀ y y' : Reds D T.rank S.rank, (∀ PP ∈ B.de.Q ∪ Q', y PP = y' PP) →
      B.locFn Q' (fun PP => φ PP.1) y = B.locFn Q' (fun PP => φ PP.1) y' := fun y y' hy => by
    unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)],
      Finset.prod_congr (s₁ := Finset.univ) rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]]
  have hP := hQ.1
  have hPb := hP.mono hQb
  unfold Base.vecAt Frame.vec
  rw [hL, datumFn_eq_restrict hB.frame hP hQb hω]
  have hmodel := Frame.isPlaceModel_placeMap hB.frame hP
  rw [halfIdem_eq_add hQb] at hmodel ⊢
  have hm' := isPlaceModel_restrictHalf hPb.isOrthSum.1.idem (idem_mul_self_of (hP.empty_sdiff (Qb := B.de.Q ∪ Q')))
    (halfIdem_mul_idem hP hQb) (fun e he u hu => GlobalTheory.PlaceModelSum.idem_smul_latO he hu) hmodel
  exact GlobalTheory.PlaceVec.placeModel_unique hB.frame.vac.1 hB.frame.sdS hB.frame.sdT hPb.isOrthSum.1.idem
    hPb.isOrthSum.1.infPart_eq hm' (Frame.isPlaceModel_placeMap hB.frame hPb) (Frame.isSBHalf_datumFn hB.frame hPb hω)

end GlobalTheory.ExportSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValMulSqrtUnit
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UnitOverP

theorem val_eq_one_of_pow (A : ValuationSubring ℂ) {z : ℂ} {m : ℕ} (hm : m ≠ 0) (h : A.valuation (z ^ m) = 1) :
    A.valuation z = 1 := by
  rw [map_pow] at h
  exact ((pow_eq_one_iff).1 h).resolve_right hm

theorem exists_gen {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ h : ℕ, 0 < h ∧ ∃ α : 𝓞 K, Ideal.span {α} = P.asIdeal ^ h := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 K))
  have hPh : P.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 K)) := pow_mem hP h
  have h1 : ClassGroup.mk0 ⟨P.asIdeal ^ h, hPh⟩ = 1 := by
    have e : (⟨P.asIdeal ^ h, hPh⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨P.asIdeal, hP⟩ ^ h := Subtype.ext (by simp)
    rw [e, map_pow, pow_card_eq_one]
  haveI := (ClassGroup.mk0_eq_one_iff hPh).1 h1
  exact ⟨h, Fintype.card_pos, _, Ideal.span_singleton_generator _⟩

end GlobalTheory.UnitOverP

namespace GlobalTheory.UnitOverP


open Formalism.L2.Host in
theorem val_mul_sqrt_unit : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq (B.mu * B.eta⁻¹) χ → ∀ (p : ℕ) (A : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ bad : ℕ, p ∣ bad → (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q → (bad : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ P.asIdeal → ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ A ∧ (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ A := by
  intro D V W B hB χ hχ p A hp hpA bad hpb hbad P hP
  classical
  have hpP : ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    apply hP
    obtain ⟨r, rfl⟩ := hpb
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  have hinf : ∀ τ, HasInfExp D (B.mu * B.eta⁻¹) τ
      (((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) + -(1 / 2)) := fun τ =>
    GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.RealFockAction.hasInfExp_mul_of_isOpen_ker (hB.inf τ) hB.de.isOpen)
      (GlobalTheory.Chain.StepVac.hasInfExp_inv (hB.eta.2.2.2 τ))
  obtain ⟨n, -, hχinf⟩ := GlobalTheory.HeckeInfExp.hasInfQ_of_hasInfExp D _ χ _ hχ hinf
  obtain ⟨h, hh, α, hα⟩ := exists_gen P
  have hα0 : (α : D.host.E) ≠ 0 := by
    intro h0
    have h1 : α = 0 := by exact_mod_cast h0
    rw [h1, Ideal.span_singleton_eq_bot.2 rfl] at hα
    exact (pow_ne_zero h P.ne_bot) hα.symm
  set k : D.host.Eˣ := Units.mk0 _ hα0 with hk
  have hmem : ∀ v : HeightOneSpectrum (𝓞 D.host.E), α ∈ v.asIdeal ↔ v = P := by
    intro v
    constructor
    · intro hv
      have h1 : P.asIdeal ^ h ≤ v.asIdeal := by
        rw [← hα, Ideal.span_le, Set.singleton_subset_iff]; exact hv
      have h2 : P.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le h1
      exact HeightOneSpectrum.ext ((P.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)
    · rintro rfl
      have h1 : α ∈ Ideal.span {α} := Ideal.subset_span rfl
      rw [hα] at h1
      exact Ideal.pow_le_self hh.ne' h1
  have hval : ∀ v : HeightOneSpectrum (𝓞 D.host.E), v.valuation D.host.E (k : D.host.E) = v.intValuation α := fun v =>
    HeightOneSpectrum.valuation_of_algebraMap v α
  have hv1 : ∀ v, v ≠ P → v.valuation D.host.E (k : D.host.E) = 1 := fun v hv => by
    rw [hval]
    exact le_antisymm (v.intValuation_le_one α)
      (not_lt.1 fun h' => hv ((hmem v).1 ((v.intValuation_lt_one_iff_mem α).1 h')))
  have hord : ∀ v, v ≠ P → ordF v k = 0 := fun v hv => by
    unfold ordF; rw [hv1 v hv]; simp
  have hatFin : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.Eˣ),
      Valued.v ((atFin v x : (v.adicCompletion D.host.E)ˣ) : v.adicCompletion D.host.E) = v.valuation D.host.E (x : D.host.E) :=
    fun v x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : D.host.E)
  set N := ordF P k with hNdef
  have hPv : P.valuation D.host.E (k : D.host.E) = WithZero.exp (-N) := by
    have h0 : P.valuation D.host.E (k : D.host.E) ≠ 0 := by simp
    rw [hNdef, ordF, neg_neg]
    exact (WithZero.exp_log h0).symm
  have hN : 0 < N := by
    have h1 : P.valuation D.host.E (k : D.host.E) < 1 := by
      rw [hval]; exact (P.intValuation_lt_one_iff_mem α).2 ((hmem P).2 rfl)
    rw [hPv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    omega

  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  set S := insert P hfin.toFinset with hSdef
  have hS : ∀ v, v ∉ S → χ.UnrAt v := fun v hv => by
    by_contra h'
    exact hv (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 h'))
  have hpr := χ.productRule S hS k
  have hfp : (∏ᶠ (v : HeightOneSpectrum (𝓞 D.host.E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      rw [finprod_eq_if]
      split_ifs with hv
      · rfl
      · rw [hord v (fun e => hv (e ▸ Finset.mem_insert_self _ _)), zpow_zero]
  rw [hfp, mul_one, ← Finset.mul_prod_erase S _ (Finset.mem_insert_self P _)] at hpr
  set u : D.host.Eˣ := k * (unif P ^ N)⁻¹ with hudef
  have hku : k = u * unif P ^ N := by rw [hudef, inv_mul_cancel_right]
  have hlocP : χ.locK P k = χ.locK P u * χ.val P ^ N := by
    rw [hku, map_mul, map_zpow]; rfl
  have hu : IsUnitAt P (atFin P u) := by
    have h1 := unif_spec P
    unfold IsUnifAt at h1
    unfold IsUnitAt
    rw [hudef, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h1, hatFin, hPv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hroot : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.Eˣ), IsUnitAt v (atFin v x) →
      A.valuation ((χ.locK v x : ℂˣ) : ℂ) = 1 := by
    intro v x hx
    obtain ⟨m, hm, hxm⟩ := _root_.GlobalTheory.LocUnitPow.loc_pow_eq_one _ χ v _ hx
    apply val_eq_one_of_pow A hm.ne'
    rw [← Units.val_pow_eq_pow_val, show χ.locK v x = χ.loc v (atFin v x) from rfl, hxm, Units.val_one, map_one]
  have hw : ∀ τ, A.valuation (tauE D τ (k : D.host.E) / ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ)) = 1 := by
    intro τ
    apply val_eq_one_of_pow A two_ne_zero
    have hz : tauE D τ (k : D.host.E) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    have hz' : starRingEnd ℂ (tauE D τ (k : D.host.E)) ≠ 0 := (map_ne_zero _).2 hz
    have hn : ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ) ^ 2 = tauE D τ (k : D.host.E) * starRingEnd ℂ (tauE D τ (k : D.host.E)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have e : (tauE D τ (k : D.host.E) / ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ 2 =
        tauE D τ (k : D.host.E) / starRingEnd ℂ (tauE D τ (k : D.host.E)) := by
      rw [div_pow, hn]; field_simp
    have h1 : A.valuation (tauE D τ (k : D.host.E)) = 1 := _root_.GlobalTheory.valuation_embedding_generator_eq_one _ A p hp hpA P hpP α h hα (tauE D τ)
    have h2 : A.valuation (starRingEnd ℂ (tauE D τ (k : D.host.E))) = 1 :=
      _root_.GlobalTheory.valuation_embedding_generator_eq_one _ A p hp hpA P hpP α h hα ((starRingEnd ℂ).comp (tauE D τ))
    rw [e, map_div₀, h1, h2, div_one]
  have hinfv : A.valuation ((χ.inf k : ℂˣ) : ℂ) = 1 := by
    rw [hχinf k, map_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [map_zpow₀, hw τ, _root_.one_zpow]
  have hrest : A.valuation ((∏ v ∈ S.erase P, χ.locK v k : ℂˣ) : ℂ) = 1 := by
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => hroot v k ?_
    unfold IsUnitAt
    rw [hatFin]
    exact hv1 v (Finset.ne_of_mem_erase hv)
  have key := congrArg (fun x : ℂˣ => A.valuation (x : ℂ)) hpr
  simp only [hlocP, Units.val_mul, map_mul, Units.val_one, map_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hinfv, hrest,
    hroot P u hu, one_mul, mul_one] at key
  have hvalP : A.valuation ((χ.val P : ℂˣ) : ℂ) = 1 := by
    obtain ⟨M, hM⟩ := Int.eq_ofNat_of_zero_le hN.le
    rw [hM, zpow_natCast] at key
    refine val_eq_one_of_pow A (m := M) (by have h3 := hN; rw [hM] at h3; omega) ?_
    rw [map_pow]; exact key
  have hfinal : A.valuation (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
    rw [map_mul, hvalP, _root_.GlobalTheory.valuation_sqrt_absNorm_eq_one _ A p hp hpA P hpP, one_mul]
  exact ⟨(A.valuation_le_one_iff _).1 hfinal.le, (A.valuation_le_one_iff _).1 (by rw [map_inv₀, hfinal, inv_one])⟩

end GlobalTheory.UnitOverP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

def trSp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (e : AE D) (M : ℕ) (O : Subring ℂ) :
    Submodule O (WO V W → ℂ) :=
  Submodule.span O {f | ∃ y : WO V W, IsHalf e y ∧ M • y ∈ latO V W ΛV ΛW (fun _ => True) ∧ f = heisO ψ V W y f₀}

abbrev stdF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (sW BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) :
    MvPolynomial (FVar D W.rank V.rank) ℂ →ₗ[ℂ] (WO V W → ℂ) :=
  pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW f

def OneAt (V : HSp D) (l : ℕ) (h : GA D V) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
    ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V h - 1) a b = 0

def ChiData (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) : Prop :=
  ChrEq χW χ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((b : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1

def ValRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ) : Prop :=
  ∀ x : k, la.valuation k x ≤ 1 → σ x ∈ O

def locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) : Subring ℂ :=
  (la.valuation k).integer.map σ

theorem valRing_locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la (locRing σ la) := fun x hx => ⟨x, hx, rfl⟩

theorem valRing_range {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la σ.range := fun x _ => ⟨x, rfl⟩

def ConjIn (D : D7) {k : Type} [Field k] (σ : k →+* ℂ) : Prop := ∀ (τ : D.host.E →+* ℂ) (a : D.host.E), ∃ x, σ x = τ a

def DenomAt {E : Type} [Field E] {n : ℕ} (l c : ℕ) (γ : GL (Fin n) E) : Prop :=
  ∃ m : ℕ, Nat.Coprime m l ∧ ∀ a b, IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ.val a b) ∧
    IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ⁻¹.val a b)

theorem oneAt_one (V : HSp D) (l : ℕ) : OneAt V l 1 := fun _ _ _ _ a b => by
  have h1 : Formalism.L2.Theta.mt V 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  rw [h1, sub_self]
  simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
  (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i)

def BaseCc (ph : ℂ) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) T.σ₀) (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * T.cE ((i : ℕ) + 1) T.σ₀ k

def CovCc (ph : ℂ) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂)
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * C.cc₂ k

end GlobalTheory.LevelSeries

end
end

