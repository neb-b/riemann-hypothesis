module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzMemSpanDatumTranslates
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.LatHalf

open GlobalTheory.ExportSeries
open Formalism.L2.DIV (Pl)

variable {D : D7}

theorem levConj_conjPl (P : Formalism.L2.DIV.Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl P (Formalism.L2.DIV.conjPl P) := by
  intro c hc
  refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ P.asIdeal
  rw [Formalism.L2.DIV.starO_starO]
  exact hc

theorem eq_conjPl_of_levConj {A B : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl A B) :
    B = Formalism.L2.DIV.conjPl A := by
  refine (HeightOneSpectrum.ext ?_).symm
  refine Ideal.IsMaximal.eq_of_le (Formalism.L2.DIV.conjPl A).isMaximal B.isPrime.ne_top fun b hb => ?_
  obtain ⟨c', hc', e⟩ := h (Formalism.L2.DIV.starO b) hb
  have : c' = b := RingOfIntegers.ext (by rw [e, Formalism.L2.DIV.starO_coe, star_star])
  exact this ▸ hc'

theorem isIdemAt_conjPl {e : AE D} {P : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e P) :
    Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.L2.DIV.conjPl P) :=
  GlobalTheory.MovedIdem.isIdemAt_conj h fun x => by
    rw [show Formalism.L2.Col.cO D.host.E x = Formalism.L2.DIV.starO x from RingOfIntegers.ext (by rw [Formalism.L2.DIV.starO_coe]; rfl)]
    rfl

theorem conj_placesOK {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) :
    idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) ∧ PlacesOK ∅ (Pg.image Formalism.L2.DIV.conjPl) := by
  obtain ⟨P, h1, -, hP⟩ := h.split
  have hS := hP.mono h1
  have hinj : Set.InjOn Formalism.L2.DIV.conjPl (Pg : Set (Pl D.host.E)) := fun a _ b _ hab => by
    rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl]
  have hc : ∀ PP ∈ Pg, idemAt (Formalism.L2.DIV.conjPl PP) = cA D (idemAt PP) := fun PP hPP =>
    idemAt_eq (isIdemAt_conjPl (hS.isIdemAt hPP))
  have he : idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [idem, Finset.sum_image hinj, idem, map_sum]
    exact Finset.sum_congr rfl hc
  refine ⟨he, ⟨⟨Pg.image Formalism.L2.DIV.conjPl, Finset.empty_subset _, le_rfl,
    ⟨idem (Pg.image Formalism.L2.DIV.conjPl), ⟨idemAt, ?_, rfl⟩, ?_⟩⟩, Finset.disjoint_empty_left _, ?_⟩⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    rw [hc P0 hP0]
    exact isIdemAt_conjPl (hS.isIdemAt hP0)
  · rw [he, GlobalTheory.DualPairCheck.cA_cA, mul_comm]
    exact hS.isIdemSum.2
  · intro PP hPP PP' hPP'
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 (hPP.resolve_left (Finset.notMem_empty PP))
    rcases hPP' with rfl | hc'
    · exact h.prime P0 (Or.inl hP0) _ (Or.inr (levConj_conjPl P0))
    · rw [eq_conjPl_of_levConj hc', Formalism.L2.DIV.conjPl_conjPl]
      exact h.prime P0 (Or.inl hP0) P0 (Or.inl rfl)

theorem goodPosition_auxiliaryPlaces_alone {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) : PlacesOK ∅ Q :=
  ⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _,
    fun PP hPP => h.prime PP (Or.inr (hPP.resolve_left (Finset.notMem_empty PP)))⟩

theorem idem_sq {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) : idem R * idem R = idem R := by
  have := h.isOrthSum.1.idem
  rwa [halfIdem, idem_empty, map_zero, zero_add] at this

theorem toEAf_idem_int {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) :
    toEAf D (idem R) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, -, h2, hP⟩ := h.split
  have := GlobalTheory.DatumFourier.idem_div_int (hP.mono h2).isIdemSum one_ne_zero fun PP _ hPP =>
    PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hPP))
  simpa using this

theorem frMapO_add {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (x : Mx D m n) : IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, he]

theorem mem_lat_piece {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    (x : WO S T) (hi : IsIntM (frMapO S T F.βS F.βT x)) : idem R • x ∈ F.lat := by
  refine _root_.GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int hF hR (isHalf_smul (idem_sq hR) x) ?_
  rw [frMapO_smul]
  exact fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (toEAf_idem_int hR) (hi i j)

theorem mem_lat_iff_isIntM_halfIdem : ∀ {D : D7} {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T}, F.Good →
    ∀ {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}, GlobalTheory.ExportSeries.PlacesOK Pg Q →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) →
    ∀ {x : WO S T}, IsHalf (GlobalTheory.ExportSeries.halfIdem Pg Q) x →
      (x ∈ F.lat ↔ IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) := by
  intro D S T F hF Pg Q h _ x hx
  obtain ⟨hR1, hR⟩ := conj_placesOK h
  have hQ := goodPosition_auxiliaryPlaces_alone h
  have hxe : x = idem (Pg.image Formalism.L2.DIV.conjPl) • x + idem Q • x := by
    rw [← add_smul, hR1]
    exact (Matrix.ext fun i j => hx i j).symm
  constructor
  · intro hl
    obtain ⟨o1, a1⟩ := _root_.GlobalTheory.LatHalfInt.frMap_int_of_mem_lat hF hR (isHalf_smul (idem_sq hR) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hR) hl)
    obtain ⟨o2, a2⟩ := _root_.GlobalTheory.LatHalfInt.frMap_int_of_mem_lat hF hQ (isHalf_smul (idem_sq hQ) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hQ) hl)
    rw [hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add]
    exact ⟨fun i j => add_mem (a1 i j) (a2 i j), fun i j => add_mem (o1 i j) (o2 i j)⟩
  · rintro ⟨-, hi⟩
    rw [hxe]
    exact add_mem (mem_lat_piece hF hR x hi) (mem_lat_piece hF hQ x hi)

end GlobalTheory.ExportSeries.LatHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanTranslatesConjugateHalfTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section
namespace GlobalTheory.DownLift.ConjHalfGen

theorem lowZero_map_iff {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : LowZero k (y.map f) ↔ LowZero k y := by
  unfold LowZero
  simp only [Matrix.map_apply, map_eq_zero_iff f f.injective]

theorem topL_map {A B : Type} [Zero A] [Zero B] (f : A → B) (hf : f 0 = 0) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : topL k (y.map f) = (topL k y).map f := by
  ext i j
  simp only [topL, Matrix.map_apply]
  split_ifs <;> simp [hf]

theorem det_topL_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : (topL k (y.map f)).det = f (topL k y).det := by
  rw [topL_map f (map_zero f), RingHom.map_det]
  rfl

theorem det_topL_mapE {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : (topL k (y.map f)).det = f (topL k y).det :=
  det_topL_map (f : A →+* B) k y

theorem omegaQ_single {D : D7} {a b : ℕ} (PP : Pl D.host.E) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : LowZero r (y PP)) (u : (kP PP)ˣ)
    (hu : (u : kP PP) = (topL r (y PP)).det) :
    omegaQ {PP} r ξ (-1) y = ((ξ PP u : ℂˣ) : ℂ)⁻¹ := by
  have h : ∀ PP' ∈ ({PP} : Finset (Pl D.host.E)), LowZero r (y PP') ∧ IsUnit (topL r (y PP')).det := by
    intro PP' hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨hz, hu ▸ u.isUnit⟩
  unfold omegaQ
  rw [dite_eq_left h, Finset.prod_eq_single ⟨PP, Finset.mem_singleton_self PP⟩]
  · rw [_root_.zpow_neg_one]
    congr 4
    ext
    simp [hu]
  · intro x _ hx
    exfalso
    exact hx (Subtype.ext (Finset.mem_singleton.1 x.2))
  · intro hx
    exact absurd (Finset.mem_attach _ _) hx

theorem omegaQ_ne_zero {D : D7} {a b : ℕ} (PP : Pl D.host.E) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (h : omegaQ {PP} r ξ k y ≠ 0) :
    LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det := by
  unfold omegaQ at h
  split_ifs at h with h'
  · exact h' PP (Finset.mem_singleton_self PP)
  · exact absurd rfl h

end GlobalTheory.DownLift.ConjHalfGen
end

noncomputable section
namespace GlobalTheory.DownLift.ConjHalfGen


set_option maxHeartbeats 1000000 in
theorem mem_span_translT : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), T.rank ≤ S.rank → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ N : ℕ, IsBaseFrame S βS ΛS N → Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∀ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ, ξ PP ≠ 1 → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → (∀ κ : GA D S, SuppAt e S κ → κ ∈ GfC S → finE S κ ∈ St βS → redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) → (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) → ∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → Φ (actO S T κ 1 x) * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) x' = Φ x * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) (actO S T κ 1 x')) → Φ ∈ Submodule.span ℂ (translT S T (cA D e) (adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)))) := by
  classical
  intro D S T βS βT hrn ΛS ΛT N hBF hLS hLT e PP hidem ξ hξ Φ hΦ hlaw
  obtain ⟨v, φ, ι, hch⟩ := GlobalTheory.T.exists_idempotentPlaceChart_finiteAdeles D e PP hidem
  obtain ⟨hsurj, hinj, hint, hred⟩ := _root_.GlobalTheory.DownLift.ReadAdj.rdAdj_read D S T βS βT e PP v φ ι hidem hch
  haveI : Finite (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) := Finite.of_equiv _ ι.toEquiv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (GlobalTheory.SplitHecke.Ov D v)
  choose σ hσH hσ using hsurj
  set ω := omegaQ {PP} T.rank ξ (-1) with hω
  set Φ' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ := fun m => Φ (σ m) with hΦ'
  set Φ₀' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ := fun m => adjDat S T βS βT e ω (σ m) with hΦ₀'
  set ξ' : (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))ˣ →* ℂˣ :=
    (ξ PP).comp (Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom) with hξ'
  have hξ'1 : ξ' ≠ 1 := by
    intro h1
    apply hξ
    ext u
    have h2 := DFunLike.congr_fun h1 (Units.map (ι : kP PP ≃+* _).toMonoidHom u)
    have h3 : Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom
        (Units.map (ι : kP PP ≃+* _).toMonoidHom u) = u := by
      ext; simp
    simp only [hξ', MonoidHom.comp_apply, h3, MonoidHom.one_apply] at h2
    rw [h2]; rfl

  have hA : ∀ (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)) (u : (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))ˣ),
      LowZero T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) →
      (u : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) = (topL T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))).det →
      Φ₀' (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v))) = ((ξ' u : ℂˣ) : ℂ)⁻¹ := by
    intro z u hz hu
    set x := σ (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxH := hσH (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxr := hσ (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxI : IsIntM (frMapAdj S T βS βT x) := (hint x hxH).2 ⟨z, hxr⟩
    have hxR := hred x z hxI hxr
    have hLZ : LowZero T.rank (redM PP (frMapAdj S T βS βT x)) := by
      rw [← lowZero_map_iff ι, hxR]; exact hz
    have hdet : ι (topL T.rank (redM PP (frMapAdj S T βS βT x))).det = (u : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) := by
      rw [hu, ← hxR, det_topL_mapE ι]
    show adjDat S T βS βT e ω x = _
    unfold adjDat
    rw [if_pos ⟨hxH, hxI⟩, hω, omegaQ_single PP T.rank ξ _ hLZ
      (Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom u)]
    · rfl
    · simp [← hdet]
  have hB : ∀ m, Φ₀' m ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
      m = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) ∧
      LowZero T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) ∧
      IsUnit (topL T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))).det := by
    intro m hm
    have hm' : adjDat S T βS βT e ω (σ m) ≠ 0 := hm
    unfold adjDat at hm'
    split_ifs at hm' with hc
    · obtain ⟨z, hz⟩ := (hint (σ m) hc.1).1 hc.2
      have hR := hred (σ m) z hc.2 hz
      obtain ⟨h1, h2⟩ := omegaQ_ne_zero PP T.rank ξ (-1) _ hm'
      refine ⟨z, by rw [← hz, hσ], ?_, ?_⟩
      · rw [← hR, lowZero_map_iff ι]; exact h1
      · rw [← hR, det_topL_mapE ι]; exact h2.map _
    · exact absurd rfl hm'

  have hC : ∃ N : ℕ, (∀ m (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)),
      Φ' (m + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v))) = Φ' m) ∧
      ∀ m, Φ' m ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
        algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) (ϖ ^ N) • m = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
    obtain ⟨N', hinv, hsupp⟩ := GlobalTheory.T.schwartzBruhat_conjHalf_locallyConstant_compactSupport D S T βS βT e PP v φ ι hidem hch ΛS ΛT (by first | exact hLS | exact hLS.toIsLattice) (by first | exact hLT | exact hLT.toIsLattice) Φ hΦ ϖ hϖ
    refine ⟨N', fun m z => ?_, fun m hm => ?_⟩
    · exact hinv (σ m) _ (hσH m) (hσH _) z (by rw [hσ, hσ])
    · obtain ⟨z, hz⟩ := hsupp (σ m) hm
      exact ⟨z, by rw [← hσ m]; exact hz⟩

  have hD : ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), LowZero T.rank (h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) →
      ∀ m m' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v),
      Φ' (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * m) * Φ₀' m' =
        Φ' m * Φ₀' (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * m') := by
    intro h hLZ m m'
    obtain ⟨κ, hsupp, hGf, hSt, hrκ, hoth, hact⟩ := _root_.GlobalTheory.DownLift.SplitCoef.exists_supp_lift_adj D S T βS βT e PP v φ ι hidem hch ΛS N hBF h
    have hBT : redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) := by
      rw [mem_blockTri]
      intro i j hij
      have hj : j.val < T.rank := by
        by_contra hj; simp only [blk2, if_neg hj] at hij; split_ifs at hij <;> omega
      have hi : T.rank ≤ i.val := by
        by_contra hi; simp only [blk2, if_pos (Nat.lt_of_not_le hi)] at hij; omega
      have h1 := congrFun (congrFun hrκ i) j
      simp only [Matrix.map_apply] at h1
      have h4 := hLZ i j hi hj
      simp only [Matrix.map_apply] at h4
      exact ι.injective ((h1.trans h4).trans (map_zero ι).symm)
    have hmove : ∀ y, σ (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * y) = actO S T κ 1 (σ y) := by
      intro y
      refine hinj _ _ (hσH _) (GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσH y)) ?_
      rw [hσ, hact, hσ]
    show Φ (σ _) * adjDat S T βS βT e ω (σ m') = Φ (σ m) * adjDat S T βS βT e ω (σ _)
    rw [hmove, hmove]
    exact hlaw κ hsupp hGf hSt hBT hoth (σ m) (σ m') (hσH m) (hσH m')
  have hpure := _root_.GlobalTheory.parahoric_schwartz_mem_span_datum_translates (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) S.rank T.rank hrn ϖ hϖ ξ' hξ'1 Φ' Φ₀' hA hB hC hD

  let L : ((Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := fun Ψ x => if IsHalf (cA D e) x then Ψ (rdAdj S T βS βT φ x) else 0
      map_add' := fun Ψ Ψ' => by funext x; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c Ψ => by funext x; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hLΦ : L Φ' = Φ := by
    funext x
    show (if IsHalf (cA D e) x then Φ (σ (rdAdj S T βS βT φ x)) else 0) = Φ x
    split_ifs with hx
    · rw [hinj _ x (hσH _) hx (hσ _)]
    · by_contra hne
      exact hx (hΦ.1 x (Ne.symm hne))
  have hmem := Submodule.mem_map_of_mem (f := L) hpure
  rw [Submodule.map_span, hLΦ] at hmem
  refine Submodule.span_mono ?_ hmem
  rintro _ ⟨Ψ, ⟨γ, rfl⟩, rfl⟩
  obtain ⟨g, hgs, hgx⟩ := _root_.GlobalTheory.DownLift.SplitCoef.exists_supp_rdAdj_mul D S T βS βT e PP v φ ι hidem hch γ
  refine ⟨g, ?_, ?_⟩
  · intro i j
    have := hgs i j
    rwa [Formalism.L2.Theta.cA_cA, add_comm]
  · funext x
    show (if IsHalf (cA D e) x then adjDat S T βS βT e ω (σ (rdAdj S T βS βT φ x * γ.val)) else 0) = adjDat S T βS βT e ω (actO S T 1 g x)
    split_ifs with hx
    · have hgH := GlobalTheory.SplitHecke.isHalf_actO 1 g hx
      rw [hinj _ (actO S T 1 g x) (hσH _) hgH (by rw [hσ, hgx])]
    · have hgH : ¬ IsHalf (cA D e) (actO S T 1 g x) := by
        intro h'
        have := GlobalTheory.SplitHecke.isHalf_actO (1 : GA D S)⁻¹ g⁻¹ h'
        rw [GlobalTheory.SplitHecke.actO_inv_actO] at this
        exact hx this
      unfold adjDat
      rw [if_neg (fun h' => hgH h'.1)]

end GlobalTheory.DownLift.ConjHalfGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetValue

open GlobalTheory.SplitHecke

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_unit (u : (v.adicCompletionIntegers F)ˣ) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) u) = 1 := by
  by_contra hne
  exact (GlobalTheory.SplitUnif.mem_max v u).2 (lt_of_le_of_ne (u : v.adicCompletionIntegers F).2 hne) u.isUnit

theorem valued_irreducible {p : v.adicCompletionIntegers F} (hp : Irreducible p) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) p) = WithZero.exp (-1) := by
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  let p₀ : v.adicCompletionIntegers F := ⟨algebraMap F (Fv F v) t, GlobalTheory.SplitUnif.map_mem v _ t⟩
  have hp₀ : Valued.v (p₀ : Fv F v) = WithZero.exp (-1) := (hφ t).trans ht
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hp
    (GlobalTheory.SplitUnif.irreducible_of_valued v p₀ hp₀)
  have := congrArg (fun y : v.adicCompletionIntegers F => Valued.v (y : Fv F v)) hw
  change Valued.v ((p : Fv F v) * (w : v.adicCompletionIntegers F)) = Valued.v (p₀ : Fv F v) at this
  rw [map_mul, hp₀] at this
  have hw1 := valued_unit v w
  rw [← this]
  change _ = _ * Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) w)
  rw [hw1, mul_one]
  rfl

theorem card_residue_eq :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap F (Fv F v)) v (fun _ => rfl) fun s => by
    rw [hφ, HeightOneSpectrum.intValuation_lt_one_iff_mem]

end Local

section Chart

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem chi_of_unit_gen (hπ : Chart e v π) {x d : (AE D)ˣ} (hx1 : (1 - e) * (x : AE D) = 1 - e)
    (hd1 : (1 - e) * (d : AE D) = 1 - e) {A : Type} [CommGroup A] {χ : (AE D)ˣ →* A}
    (hχ : ∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D →
      finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) {u : (Ov D v)ˣ}
    (h1 : π (d : AE D) = π (x : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u) : χ d = χ x := by
  have h3 : π ((x⁻¹ * d : (AE D)ˣ) : AE D) = algebraMap (Ov D v) (Fv D.host.F v) u := by
    rw [Units.val_mul, π.map_mul, h1, ← mul_assoc, ← π.map_mul, Units.inv_mul, π.map_one, one_mul]
  have h4 := hχ (x⁻¹ * d) ?_ ((hπ.2.2.2 _).2 ⟨u, h3.symm⟩) ((hπ.2.2.2 _).2 ⟨(u⁻¹ : (Ov D v)ˣ), ?_⟩)
  · rwa [χ.map_mul, χ.map_inv, inv_mul_eq_one, eq_comm] at h4
  · have h5 : (1 - e) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
      conv_lhs => rw [← hx1, mul_assoc, Units.mul_inv, mul_one]
    rw [Units.val_mul, ← mul_assoc, h5, hd1]
  · rw [map_units_inv, map_units_inv, h3]

end Chart


set_option maxHeartbeats 1000000 in
theorem det_modulus_chi : ∀ (D : D7) (V : HSp D) (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ (k : ℕ) (α : GA D V), IsHeckeElt V e (ϖ : D.host.E) k α → ∀ k₁ ∈ Mult.locPart V (KsphC V ∅) e, ∀ k₂ ∈ Mult.locPart V (KsphC V ∅) e, ∀ z : (AE D)ˣ, IsDetAt e V (k₁ * α * k₂) z → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = (((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ k)⁻¹ ∧ ∀ (A : Type) [CommGroup A] (χ : (AE D)ˣ →* A), (∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D → finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) → χ z = χ x ^ k := by
  intro D V P e hP ϖ hϖ hϖ2 x hx k α hα k₁ hk₁ k₂ hk₂ z hz
  have he := hP.1
  obtain ⟨v, π, hπ⟩ := _root_.GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨⟨p, hpϖ, hp⟩, hq⟩ := _root_.GlobalTheory.SplitUnif.unif_chart e P v π hP hπ ϖ hϖ hϖ2
  obtain ⟨β, hβ⟩ := _root_.GlobalTheory.SplitFrame.exists_frame e v π he hπ V
  have st := _root_.GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ V β hβ
  have hH : Hk (Ov D v) p k (rho V π β (k₁ * α * k₂)) := by
    rw [map_mul, map_mul]
    exact (GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π he hπ V β hβ (ϖ : D.host.E) p k α hpϖ hα).mul ((st _ hk₁.2).1 hk₁.1)
      ((st _ hk₂.2).1 hk₂.1)
  obtain ⟨u, hu⟩ := hH.2.2
  have hx1 : (1 - e) * (x : AE D) = 1 - e := by
    rw [hx]
    exact one_sub_mul_idem he.1 _
  have hx2 : π x = algebraMap (Ov D v) (Fv D.host.F v) p := by
    rw [hx, map_add π, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero, hpϖ]
  have hz1 : (1 - e) * (z : AE D) = 1 - e := by
    rw [hz]
    exact one_sub_mul_idem he.1 _
  have hz2 : π (z : AE D) = algebraMap (Ov D v) (Fv D.host.F v) (p ^ k * u) := by
    rw [rho_val, Matrix.det_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul] at hu
    rw [hz, map_add π, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact hu
  refine ⟨?_, fun A _ χ hχ => ?_⟩
  · rw [GlobalTheory.SplitLinear.absFin_split D e v π he hπ z hz1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have e1 : ((Units.map π.toMonoidHom z : (Fv D.host.F v)ˣ) : Fv D.host.F v) = π (z : AE D) := rfl
    have e2 : Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
      rw [← card_residue_eq, hq]
    have hv1 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) p) = WithZero.exp (-1) := valued_irreducible v hp
    have hv2 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) u) = 1 := valued_unit v u
    rw [e1, hz2, map_mul, map_mul, map_pow, map_pow, hv1, hv2, mul_one, e2,
      ← WithZero.exp_nsmul, WithZero.log_exp, nsmul_eq_mul, mul_neg_one, _root_.zpow_neg, zpow_natCast]
  · have h1 : π (z : AE D) = π ((x ^ k : (AE D)ˣ) : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u := by
      rw [hz2, Units.val_pow_eq_pow_val, π.map_pow, hx2, ← RingHom.map_pow, ← RingHom.map_mul]
    have h2 : ∀ j : ℕ, (1 - e) * ((x ^ j : (AE D)ˣ) : AE D) = 1 - e := fun j => by
      induction j with
      | zero => rw [pow_zero, Units.val_one, mul_one]
      | succ j ih => rw [pow_succ, Units.val_mul, ← mul_assoc, ih, hx1]
    exact (chi_of_unit_gen hπ (h2 k) hz1 hχ h1).trans (χ.map_pow x k)

end GlobalTheory.SplitDetValue
end
end

