module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisRingHomBounded
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionOfJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ExtJumps

open Module Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence


set_option maxHeartbeats 1000000 in
theorem jumps_of_ses {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (Tt : LocTied l P AI)
    {K LL : FinExt l} (T T₁ T₂ : Lat K LL) (f : T.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V)
    (hses : IsSES f g) (hdr0 : IsDR (P.PD K) T.ρ) (hdr1 : IsDR (P.PD K) T₁.ρ) (hdr2 : IsDR (P.PD K) T₂.ρ)
    (τ : Emb K LL) (h2 : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₂.ρ τ b) = if b ≤ 0 then 1 else 0)
    (U : Set ℤ) (hU : (0 : ℤ) ∈ U) (hJ : JumpsInV (P.PD K) T.ρ τ U) : JumpsInV (P.PD K) T₁.ρ τ U := by
  have := K.2
  have := LL.2
  have hfin : ∀ b, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) := by
    intro b
    haveI := (_root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI Tt K LL T₁.V T₁.ρ).1
    exact Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_left)
  have key : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) =
      finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) + if b ≤ 0 then 1 else 0 := by
    intro b
    have hs : StrictAt P K LL := GlobalTheory.DRFil.strictAt Tt K LL
    have hs2 := hs T T₁ T₂ f g hses hdr0 hdr1 hdr2 τ b
    unfold SubSES at hs2
    obtain ⟨k₀, k₁, k₂⟩ := hs2
    haveI := hfin b
    have h := GlobalTheory.CrysExt.finrank_add_of_exact (LL := ↥LL.1) (mapdR P f) (mapdR P g) (FildR (P.PD K) T.ρ τ b)
      (FildR (P.PD K) T₁.ρ τ b) (FildR (P.PD K) T₂.ρ τ b) k₀ (Submodule.ext k₁) (Submodule.ext k₂)
    have h3 := h2 b
    omega
  intro b hb
  by_contra hbU
  have hTb : FildR (P.PD K) T.ρ τ (b + 1) = FildR (P.PD K) T.ρ τ b := by
    by_contra h
    exact hbU (hJ b h)
  have hb0 : b ≠ 0 := by rintro rfl; exact hbU hU
  apply hb
  haveI := hfin b
  have hle : FildR (P.PD K) T₁.ρ τ (b + 1) ≤ FildR (P.PD K) T₁.ρ τ b :=
    GlobalTheory.DRFil.FildR_antitone (P.PD K) T₁.ρ τ (Int.le_add_one le_rfl)
  have e3 : finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) :=
    congrArg (fun S : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) => finrank ↥LL.1 ↥S) hTb
  have e1 := key (b + 1)
  have e2 := key b
  have hr : finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) := by
    have h4 : (if b + 1 ≤ 0 then 1 else 0 : ℕ) = if b ≤ 0 then 1 else 0 := by
      split_ifs <;> omega
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle hr

theorem jumps_extLat : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (T : QLat LL) (U : Finset ℤ), (0 : ℤ) ∈ U → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)) → ∀ z : ↥(latticeCocycles T.L), IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ → ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z).ρ τ (U : Set ℤ) := by
  intro l _ a e _ _ ϖ LL _ _ Pl AI hstd T U hU hT hJ z hz τ
  obtain ⟨Tt⟩ := hstd
  have hK : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ (ϖ.field a).1 := bot_le
  have := (Formalism.MainNotions.ElementDenominator.qlExt l).2
  have := LL.2
  have hdr0 := GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL T (ϖ.field a) hK hT
  have hdr1 := GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL
    (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a) hK hz
  have hext := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt T.ρ ⟨(z : Gl l → T.V), z.2.1⟩
  refine jumps_of_ses Tt T (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (unitLat (Gl l))
    (LinearMap.inl ↥LL.1 T.V ↥LL.1) (LinearMap.snd ↥LL.1 T.V ↥LL.1)
    ⟨hext.1.2.2.2.1, hext.1.2.2.2.2, hext.1.1, hext.1.2.1, hext.1.2.2.1⟩ hdr0 hdr1
    (GlobalTheory.CrysExt.isDR_trivial (G := Gl l) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1)) τ
    (fun b => GlobalTheory.CrysExt.finrank_fildR_trivial (G := Gl l) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) τ b) _ hU (hJ τ)

end GlobalTheory.ExtJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscPeriodDataOfAcrisPeriods
section
attribute [local irreducible] Formalism.Per.σC Formalism.Per.σO Formalism.Per.φA Formalism.Per.zA Formalism.Per.AinfP Formalism.Per.zP Formalism.Per.toC Formalism.Per.θP Formalism.Per.kerP Formalism.Per.ev Formalism.Per.FilP Formalism.Per.θD Formalism.Per.pD Formalism.Per.zD Formalism.Per.FilD Formalism.Per.Acris0 Formalism.Per.Acris Formalism.Per.Bcris Formalism.Per.aB Formalism.Per.a0B Formalism.Per.zB Formalism.Per.φB Formalism.Per.σF Formalism.Per.σA Formalism.Per.extP Formalism.Per.σDp Formalism.Per.σD Formalism.Per.σB Formalism.Per.IsLog

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.SeedAsm

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem phiA_alg (a : Ainf l) : phiA l (algebraMap (Ainf l) (Per.Acris l) a) =
    algebraMap (Ainf l) (Per.Acris l) (WittVector.frobenius a) := by
  rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
  congr 1
  ext n
  rw [GlobalTheory.RingIface.phiA_coeff, WittVector.coeff_frobenius_charP]

theorem sigA_alg (g : Per.Gq l) (a : Ainf l) : sigA g (algebraMap (Ainf l) (Per.Acris l) a) =
    algebraMap (Ainf l) (Per.Acris l) (Per.σA g a) := by
  rw [(GlobalTheory.CrisMaps.sigA_extends g).alg]

theorem iA_injective : Function.Injective bk.iA := by
  obtain ⟨h0, h1, -, -⟩ := _root_.GlobalTheory.BSP.norm_E_le_radius l K bk (Ainf l) bk.ev
  obtain ⟨ι, ⟨tb⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  exact (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1

theorem isDomain : IsDomain (bk.DA bk.ρ₀) := by
  obtain ⟨h0, h1, -, -⟩ := _root_.GlobalTheory.BSP.norm_E_le_radius l K bk (Ainf l) bk.ev
  exact (discAinf_isDomain l K bk bk.ρ₀ h0 h1).1

variable {bk}

theorem comm_phi (γ : Per.Acris l →+* bk.DA bk.ρ₀) (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a)
    (hn : ∀ x, ‖γ x‖ ≤ 1) (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ) (x : Per.Acris l) :
    Φ (γ x) = γ (phiA l x) := by
  have h := _root_.GlobalTheory.AcrisDiscExt.acris_disc_ext l K bk (Φ.comp γ) (γ.comp (phiA l)) (fun a => by
      simp only [RingHom.comp_apply, hγ, phiA_alg]
      exact hΦ.ext a) (fun x => (hΦ.norm_le _).trans (hn x)) (fun x => hn _)
  exact RingHom.congr_fun h x

theorem comm_sig (γ : Per.Acris l →+* bk.DA bk.ρ₀) (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a)
    (hn : ∀ x, ‖γ x‖ ≤ 1) (g : Per.Gq l) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G)
    (x : Per.Acris l) : G (γ x) = γ (sigA g x) := by
  have h := _root_.GlobalTheory.AcrisDiscExt.acris_disc_ext l K bk (G.comp γ) (γ.comp (sigA g)) (fun a => by
      simp only [RingHom.comp_apply, hγ, sigA_alg]
      exact hG.ext a) (fun x => (hG.norm_le _).trans (hn x)) (fun x => hn _)
  exact RingHom.congr_fun h x

theorem acrisToDisc_image_t_eq_unit_mul_period (C : Core l) {τ : Ainf l} (hτ : bk.IsPer τ) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (hn : ∀ x, ‖γ x‖ ≤ 1) :
    ∃ ν : (bk.DA bk.ρ₀)ˣ, γ C.t = ν * bk.iA (bk.ev bk.E * τ) := by
  obtain ⟨hE, ε, η, hε, hη⟩ := hτ
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.BSP.SeedT.t_assoc_mu l K bk C γ hγ hn
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.EpsilonAssociated.mu_associated l ε C.ε hε (core_isEps l C)
  refine ⟨u⁻¹ * Units.map bk.iA.toMonoidHom v * (Units.map bk.iA.toMonoidHom η)⁻¹, ?_⟩
  have e1 : bk.ev bk.E * τ = η * mu ε := by rw [← hE, hη]; rfl
  have hu' : γ C.t * u = bk.iA (mu ε) * bk.iA v := by rw [hu, ← hv, map_mul]
  rw [e1, map_mul]
  simp only [Units.val_mul, Units.coe_map, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  have hU : (u : bk.DA bk.ρ₀) * ((u⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀) = 1 := Units.mul_inv u
  have hH : bk.iA ((η⁻¹ : (Ainf l)ˣ) : Ainf l) * bk.iA η = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  linear_combination (-(γ C.t)) * hU + ((u⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀) * hu' -
    ((u⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀) * bk.iA v * bk.iA (mu ε) * hH

theorem map_smul_hom {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem smul_cancel {R : Type} [CommRing R] [IsDomain R] {m n : Type} {c : R} (hc : c ≠ 0)
    {M M' : Matrix m n R} (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

theorem evE_mul_ne_zero {τ : Ainf l} (hτ : bk.IsPer τ) : bk.ev bk.E * τ ≠ 0 := by
  obtain ⟨hE, ε, η, hε, hη⟩ := hτ
  rw [← hE, hη]
  intro h0
  have h1 : WittVector.teichmuller l ε - 1 = 0 := (Units.mul_right_eq_zero η).1 h0
  have h2 : ε = 1 := by
    have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.1 h1)
    simpa using this
  subst h2
  exact hε.2 (by simp)

end GlobalTheory.BSP.SeedAsm


open GlobalTheory.BSP.SeedAsm in
theorem GlobalTheory.BSP.seed_of_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (N c₁ c₂ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) → X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) → ∀ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), (Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), C.t ^ N • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • Z) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N))) → Nonempty (Seed bk d ρ τ) := by
  intro l _ K bk C τ hτ d ρ N c₁ c₂ c₃ F F' X X' hF hX hnp Z Z' hZ
  obtain ⟨hZZ, hφ, hg, hf1, hf2⟩ := hZ
  haveI := isDomain bk
  obtain ⟨γ, hγ, hn⟩ := _root_.GlobalTheory.AcrisDisc.exists_acris_to_disc l K bk
  obtain ⟨ν, hν⟩ := acrisToDisc_image_t_eq_unit_mul_period C hτ γ hγ hn
  set a := bk.iA (bk.ev bk.E * τ) with ha_def
  have ha : a ≠ 0 := fun h => evE_mul_ne_zero hτ (iA_injective bk (h.trans (map_zero _).symm))
  set e := bk.iS bk.E with he_def
  have hae : a = e * bk.iA τ := by rw [ha_def, map_mul]; rfl
  have he : e ≠ 0 := fun h => ha (by rw [hae, h, zero_mul])
  have hγS : ∀ s : bk.S, γ (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) s) = bk.iS s := fun s => hγ _
  have hmapS : ∀ M : Matrix (Fin d) (Fin d) bk.S,
      (M.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map γ = M.map bk.iS := fun M => by
    ext i j; simp only [Matrix.map_apply]; exact hγS _
  choose w hw using fun i j => _root_.GlobalTheory.AcrisDisc.main l K bk C γ hγ hn (2 * N) _ (hf1 i j)
  choose w' hw' using fun i j => _root_.GlobalTheory.AcrisDisc.main l K bk C γ hγ hn (2 * N) _ (hf2 i j)
  set G := Z.map γ
  set G' := Z'.map γ
  set Xs := X.map bk.iS
  set X's := X'.map bk.iS
  have hW1 : G * Xs = e ^ (2 * N) • Matrix.of w := by
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hw i j, ← Matrix.map_apply (f := γ), Matrix.map_mul, hmapS]
  have hW1' : X's * G' = e ^ (2 * N) • Matrix.of w' := by
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hw' i j, ← Matrix.map_apply (f := γ), Matrix.map_mul, hmapS]
  have hXX : Xs * X's = ((l : bk.DA bk.ρ₀) ^ c₂ * e ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (Matrix.map · bk.iS) hX
    simp only [Matrix.map_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow, map_natCast] at this
    exact this
  have hGG : G * G' = (γ C.t) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (Matrix.map · γ) hZZ
    simp only [Matrix.map_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_pow] at this
    exact this
  obtain ⟨Lu, hLu⟩ := isUnit_l_disc l (bk.ev PowerSeries.X) bk.ρ₀
  set μ : bk.DA bk.ρ₀ := (ν : bk.DA bk.ρ₀)
  set μi : bk.DA bk.ρ₀ := ((ν⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀)
  set Li : bk.DA bk.ρ₀ := ((Lu⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀)
  have hμ : μi * μ = 1 := Units.inv_mul ν
  have hL : Li * (l : bk.DA bk.ρ₀) = 1 := by rw [← hLu]; exact Units.inv_mul Lu
  have c1 : Matrix.of w * X's = ((l : bk.DA bk.ρ₀) ^ c₂) • G := by
    apply smul_cancel (pow_ne_zero (2 * N) he)
    rw [← Matrix.smul_mul, ← hW1, Matrix.mul_assoc, hXX, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]
  have c2 : Matrix.of w * Matrix.of w' =
      ((l : bk.DA bk.ρ₀) ^ c₂ * μ ^ (2 * N) * bk.iA τ ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    apply smul_cancel (pow_ne_zero (2 * N) he)
    apply smul_cancel (pow_ne_zero (2 * N) he)
    calc e ^ (2 * N) • e ^ (2 * N) • (Matrix.of w * Matrix.of w')
        = (e ^ (2 * N) • Matrix.of w) * (e ^ (2 * N) • Matrix.of w') := by rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = G * (Xs * X's) * G' := by rw [← hW1, ← hW1', Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = ((l : bk.DA bk.ρ₀) ^ c₂ * e ^ (2 * N) * γ C.t ^ (2 * N)) • 1 := by
        rw [hXX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hGG, smul_smul]
      _ = _ := by
        rw [smul_smul, smul_smul, hν, hae]
        congr 1
        ring
  have hV : (μi ^ N • Matrix.of w) * X's = (μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) • G := by
    rw [Matrix.smul_mul, c1, smul_smul]
  refine ⟨Seed.mk N c₁ c₂ c₃ F F' hF X X' hX (fun f g => hnp _ f g) (μi ^ N • Matrix.of w)
    ((Li ^ c₂ * μi ^ N) • Matrix.of w') ?_ ?_ ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, c2, smul_smul, smul_smul]
    congr 1
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h2 : (Li * (l : bk.DA bk.ρ₀)) ^ c₂ = 1 := by rw [hL, one_pow]
    linear_combination (bk.iA τ ^ (2 * N)) * ((μi * μ) ^ N * (μi * μ) ^ N * h2 + (μi * μ) ^ N * h1 + h1)
  · intro Φ hΦ
    have hP : (Z.map γ).map Φ = (Z.map (phiA l)).map γ := by
      ext i j; simp only [Matrix.map_apply]; exact comm_phi γ hγ hn Φ hΦ _
    have hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map γ =
        F.map (bk.iS.comp PowerSeries.C) := by
      ext i j; simp only [Matrix.map_apply, RingHom.comp_apply]; exact hγ _
    have htφ : γ (phiA l C.t) = Φ μ * (bk.iS (frobS l bk.a bk.E) * a) := by
      rw [← comm_phi γ hγ hn Φ hΦ, hν, map_mul]
      congr 1
      rw [ha_def, hΦ.ext, map_mul WittVector.frobenius, ← bk.ev_frob, hτ.1, map_mul bk.iA]
      rfl
    have hyp := congrArg (Matrix.map · γ) hφ
    simp only [Matrix.map_mul, map_smul_hom, map_mul, map_pow, map_natCast, hFm, hν, htφ] at hyp
    rw [hV, map_smul_hom, hP]
    ext i j
    have hij := congrFun (congrFun hyp i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, map_mul, map_pow, map_natCast] at hij ⊢
    apply mul_left_cancel₀ (pow_ne_zero N ha)
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h3 : (Φ μi * Φ μ) ^ N = 1 := by rw [← map_mul, hμ, map_one, one_pow]
    rw [show Z.map γ = G from rfl] at hij
    linear_combination (μi ^ N * Φ μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) * hij -
      (a ^ N * (l : bk.DA bk.ρ₀) ^ c₁ * Φ μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ * (Z.map (phiA l)).map γ i j) * h1 +
      (a ^ N * bk.iS (frobS l bk.a bk.E) ^ N * μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ *
        (G * F.map (bk.iS.comp PowerSeries.C)) i j) * h3
  · intro g Gm hG
    have hP : (Z.map γ).map Gm = (Z.map (sigA (g : GQ l))).map γ := by
      ext i j; simp only [Matrix.map_apply]; exact comm_sig γ hγ hn _ Gm hG _
    have hR : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map γ =
        (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) := by
      ext i j; simp only [Matrix.map_apply, RingHom.comp_apply]; exact hγ _
    have hb : Gm a = bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by rw [ha_def]; exact hG.ext _
    have htσ : γ (sigA (g : GQ l) C.t) = Gm μ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by
      rw [← comm_sig γ hγ hn _ Gm hG, hν, map_mul, hb]
    have hyp := congrArg (Matrix.map · γ) (hg g)
    simp only [Matrix.map_mul, map_smul_hom, map_mul, map_pow, hR, hν, htσ] at hyp
    rw [hV, map_smul_hom, hP]
    ext i j
    have hij := congrFun (congrFun hyp i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, map_mul, map_pow, map_natCast] at hij ⊢
    rw [show Z.map γ = G from rfl] at hij
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h3 : (Gm μi * Gm μ) ^ N = 1 := by rw [← map_mul, hμ, map_one, one_pow]
    rw [ha_def, map_mul] at hij
    linear_combination (μi ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) * hij -
      ((bk.iA (bk.ev bk.E) * bk.iA τ) ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ *
        ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (Z.map (sigA (g : GQ l))).map γ) i j) * h1 +
      ((bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) * bk.iA (Per.σA (g : GQ l) τ)) ^ N * μi ^ N *
        (l : bk.DA bk.ρ₀) ^ c₂ * G i j) * h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

theorem frob_inverse {R : Type} [CommRing R] [IsDomain R] {d : ℕ} (Φ : R →+* R)
    (W W' B : Matrix (Fin d) (Fin d) R) (t e lam : R) (ht : t ≠ 0)
    (hW : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hB : lam • W.map Φ = W * B) (hΦ : Φ t = e * t) :
    B * W'.map Φ = (lam * e) • W' := by
  have hdet : W.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hW
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ ht h1.symm
  have h2 : W.map Φ * W'.map Φ = (e * t) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hW, ← hΦ]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h3 : W * (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hB, Matrix.smul_mul, h2, Matrix.mul_smul, hW, smul_smul, smul_smul,
      mul_assoc, sub_self]
  have h4 : W.det • (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [← Matrix.one_mul (B * W'.map Φ - (lam * e) • W'), ← Matrix.smul_mul, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h3, Matrix.mul_zero]
  rw [← sub_eq_zero]
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h5
  exact (mul_eq_zero.1 h5).resolve_left hdet

theorem radius_mem (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have h2 : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (lt_trans zero_lt_one h1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.2 (one_div_pos.2 h2))

end GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

theorem GlobalTheory.BSP.seed_frob_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  intro l _ K bk τ hτ d ρ hρ s Φ hΦ
  obtain ⟨h0, h1⟩ := GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk
  haveI := (_root_.GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  have hτ0 := (_root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).2.1
  refine GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul
    (GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) ?_
  have h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ := by
    have h3 := hΦ.ext τ
    rw [hτ.1, map_mul] at h3
    exact h3
  rw [map_pow, h2, mul_pow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.FrobRational

theorem core {S A D D' : Type} [CommRing S] [IsDomain S] [CommRing A] [IsDomain A] [CommRing D] [CommRing D']
    (ev : S →+* A) (t : S →+* D) (i : A →+* D') (j : D →+* D') (hi : Function.Injective i)
    (hj : ∀ a, j (t a) = i (ev a)) (φ : A →+* A) (Φ : D' →+* D') (Ψ : D →+* D)
    (hΦ : ∀ a, Φ (i a) = i (φ a)) (hΨ : ∀ x, Φ (j x) = j (Ψ x))
    (disj : ∀ (x y : A) (f g : D), g ≠ 0 → y ≠ 0 → i x * j g = i y * j f →
      ∃ δ a : S, δ ≠ 0 ∧ ev δ * x = ev a * y)
    {d : ℕ} (lam : S) (hlam : lam ≠ 0) (W : Matrix (Fin d) (Fin d) D') (B : Matrix (Fin d) (Fin d) S)
    (hW : i (ev lam) • W.map Φ = W * B.map (i.comp ev))
    (Y : Matrix (Fin d) (Fin d) A) (Z : Matrix (Fin d) (Fin d) D) (hY : Y.det ≠ 0)
    (hYZ : W * Z.map j = Y.map i) :
    ∃ (δ : S) (A1 : Matrix (Fin d) (Fin d) S), δ ≠ 0 ∧ ev δ • Y.map φ = Y * A1.map ev := by
  classical
  set x : Matrix (Fin d) (Fin d) D := B.map t * Z.map Ψ with hx
  set P : Matrix (Fin d) (Fin d) A := ev lam • Y.map φ with hP
  have hPx : P.map i = W * x.map j := by
    have h1 : (Y.map φ).map i = (Y.map i).map Φ := by ext a b; simp [hΦ]
    have h2 : (Z.map j).map Φ = (Z.map Ψ).map j := by ext a b; simp [hΨ]
    have h3 : (B.map t).map j = B.map (i.comp ev) := by ext a b; simp [hj]
    have h4 : P.map i = i (ev lam) • (Y.map φ).map i := by ext a b; simp [hP]
    rw [h4, h1, ← hYZ, Matrix.map_mul, ← Matrix.smul_mul, hW, h2, hx, Matrix.map_mul, h3, Matrix.mul_assoc]
  have hdet : W.det * j Z.det = i Y.det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hYZ, Matrix.det_mul]
  have hZ : Z.det ≠ 0 := fun h => hY (hi (by rw [← hdet, h, map_zero, mul_zero, map_zero]))
  have hadjY : (Y.adjugate).map i = (Y.map i).adjugate := RingHom.map_adjugate i Y
  have hadjZ : (Z.adjugate).map j = (Z.map j).adjugate := RingHom.map_adjugate j Z
  have key : (Y.adjugate * P).map i = W.det • (Z.adjugate * x).map j := by
    rw [Matrix.map_mul, Matrix.map_mul, hadjY, hadjZ, hPx, ← hYZ, Matrix.adjugate_mul_distrib, Matrix.mul_assoc,
      ← Matrix.mul_assoc W.adjugate, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have hent : ∀ p : Fin d × Fin d, ∃ δ a : S, δ ≠ 0 ∧ ev δ * (Y.adjugate * P) p.1 p.2 = ev a * Y.det := by
    intro p
    refine disj _ _ ((Z.adjugate * x) p.1 p.2) Z.det hZ hY ?_
    have h := congrFun (congrFun key p.1) p.2
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h
    rw [h, ← hdet]; ring
  choose δ a hδ ha using hent
  refine ⟨(∏ p, δ p) * lam, Matrix.of fun r c => (∏ p ∈ Finset.univ.erase (r, c), δ p) * a (r, c),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun p _ => hδ p) hlam, ?_⟩
  have h5 : ev (∏ p, δ p) • (Y.adjugate * P) =
      Y.det • (Matrix.of fun r c => (∏ p ∈ Finset.univ.erase (r, c), δ p) * a (r, c)).map ev := by
    ext r c
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, smul_eq_mul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ (r, c)), map_mul, map_mul, mul_assoc, ha (r, c)]
    ring
  have h6 := congrArg (fun M => Y * M) h5
  simp only [Matrix.mul_smul] at h6
  rw [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, smul_comm] at h6
  ext r c
  have h7 := congrFun (congrFun h6 r) c
  rw [Matrix.smul_apply, Matrix.smul_apply Y.det, smul_eq_mul, smul_eq_mul] at h7
  rw [← mul_left_cancel₀ hY h7, hP, smul_smul, map_mul]

theorem isDiscMap_comp {l : ℕ} {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] {u : A} {u' : A'}
    {u'' : A''} {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {g : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'}
    {G : Disc l u' ρ' →+* Disc l u'' ρ''} (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hG : IsDiscMap (l := _) (u := _) (ρ := _) g G) :
    IsDiscMap (l := _) (u := _) (ρ := _) (g.comp f) (G.comp F) :=
  ⟨fun a => by rw [RingHom.comp_apply, hF.ext, hG.ext, RingHom.comp_apply],
    fun x => (hG.norm_le _).trans (hF.norm_le x)⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  intro l hl K bk τ hτ d ρ hρ s Y1 Z1 hY hYZ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨ι, ⟨TB⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (_root_.GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  have hi : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB bk.ρ₀ h0 h1).1
  haveI : IsDomain (Ainf l) := hi.isDomain _
  obtain ⟨j, hj⟩ := exists_discMap_of_pow_dvd l _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0
    (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l _ _ (frobS l bk.a) (X : bk.S) (X : bk.S) bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l _ _ (WittVector.frobenius : Ainf l →+* Ainf l) (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hcomm : Φ.comp j = j.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (isDiscMap_comp hj hΦ).unique (e ▸ isDiscMap_comp hΨ hj)
  have hlam : bk.iA (bk.ev ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N)) =
      (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N := by
    simp only [map_mul, map_pow, map_natCast, RingHom.comp_apply]
  have hu : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (isUnit_toDisc_frobS_E l K bk).map j
    rwa [hj.ext] at h
  have hne : (l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N ≠ 0 := fun h => by
    rw [h, map_zero, map_zero] at hlam
    exact (((isUnit_l_disc l _ _).pow _).mul (hu.pow _)).ne_zero hlam.symm
  exact core bk.ev (toDisc l (X : bk.S) bk.ρ₀) bk.iA j hi hj.ext WittVector.frobenius Φ Ψ hΦ.ext
    (fun x => RingHom.congr_fun hcomm x) (GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries l K bk _ bk.ev ι TB j hj) _ hne s.W _
    (by rw [hlam]; exact GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) Y1 Z1 hY (hYZ j hj)

end GlobalTheory.BSP.FrobRational
end

