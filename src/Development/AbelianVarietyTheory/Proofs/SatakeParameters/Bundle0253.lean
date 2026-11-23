module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0089
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGL
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

theorem mulVec_mem_hatL_mvL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {N : ℕ} (h : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) M) :
    ((ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
      Formalism.L2.Herm.hatL (F := F) (mvL h M) := by
  unfold Formalism.L2.Herm.hatL latS at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hxM, rfl⟩ := hx
    refine Submodule.subset_span ⟨(h : Matrix (Fin N) (Fin N) E) *ᵥ x, ?_, ?_⟩
    · exact ⟨x, hxM, rfl⟩
    · exact (bc_mulVec (F := F) h x).symm
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ s ha

theorem mvL_one_lat {E : Type} [Field E] [NumberField E] {N : ℕ} (M : Submodule (𝓞 E) (Fin N → E)) : mvL 1 M = M := by
  unfold mvL
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, h⟩
    change ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y = x at h
    rw [Units.val_one, Matrix.one_mulVec] at h
    simpa [h] using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    change ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x = x
    rw [Units.val_one, Matrix.one_mulVec]

theorem latAd_mul_ratA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)),
    latAd (y * ratA F g) M = latAd y (mvL g M) := by
  intro F E _ _ _ _ _ _ N y g M
  have key : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      ((ratA F g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
        Formalism.L2.Herm.hatL (F := F) M ↔ w ∈ Formalism.L2.Herm.hatL (F := F) (mvL g M) := by
    intro w
    constructor
    · intro hw
      have := mulVec_mem_hatL_mvL g M _ hw
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec] at this
    · intro hw
      have := mulVec_mem_hatL_mvL g⁻¹ (mvL g M) w hw
      rwa [← mvL_mul, inv_mul_cancel, mvL_one_lat] at this
  unfold latAd
  congr 1
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, key]

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsSameBadComponentsSameLocalization
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG
open Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.PhiTLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locS_le_of_le {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (S : Submonoid R) {M M₁ : Submodule R W}
    (h : M ≤ Formalism.HermitianLatticesTheory.locS S M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, htx⟩ := h hx
  exact ⟨t * s, S.mul_mem ht hs, by rw [mul_smul]; exact htx⟩

theorem le_locS {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (S : Submonoid R) (M : Submodule R W) :
    M ≤ Formalism.HermitianLatticesTheory.locS S M := fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

theorem localization_eq_of_semilocalization_eq' {E : Type} [Field E] [NumberField E] [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    {Λ Λ₁ : Submodule (𝓞 E) (Fin n → E)} (h : Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal Λ₁) :
    Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ₁ := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := E) Q.asIdeal ≤ Q.asIdeal.primeCompl := by
    refine Submonoid.closure_le.2 ?_
    rintro s ⟨hs, -⟩
    exact hs
  have key : ∀ {M M₁ : Submodule (𝓞 E) (Fin n → E)}, Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal M = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal M₁ →
      Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M₁ := by
    intro M M₁ hM
    refine locS_le_of_le _ fun x hx => ?_
    have h1 : x ∈ Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal M₁ := hM ▸ le_locS _ M hx
    obtain ⟨t, ht, htx⟩ := h1
    exact ⟨t, hle ht, htx⟩
  exact le_antisymm (key h) (key h.symm)

theorem loc_mvL {E : Type} [Field E] [NumberField E] [StarRing E] (Q : Ideal (𝓞 E)) {n : ℕ} (g : GL (Fin n) E)
    {Λ Λ₁ : Submodule (𝓞 E) (Fin n → E)} (h : Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁) :
    Formalism.HermitianLatticesTheory.loc (K := E) Q (mvL g Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (mvL g Λ₁) := by
  have key : ∀ {M M₁ : Submodule (𝓞 E) (Fin n → E)}, Formalism.HermitianLatticesTheory.loc (K := E) Q M = Formalism.HermitianLatticesTheory.loc (K := E) Q M₁ →
      Formalism.HermitianLatticesTheory.loc (K := E) Q (mvL g M) ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q (mvL g M₁) := by
    intro M M₁ hM
    refine locS_le_of_le _ ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : y ∈ Formalism.HermitianLatticesTheory.loc (K := E) Q M₁ := hM ▸ le_locS _ M hy
    obtain ⟨t, ht, hty⟩ := h1
    refine ⟨t, ht, ⟨t • y, hty, ?_⟩⟩
    simp
  exact le_antisymm (key h) (key h.symm)

theorem exists_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ v : HeightOneSpectrum (𝓞 F), Formalism.L2.Col.IsOver v Q :=
  ⟨HeightOneSpectrum.under (𝓞 F) Q, rfl⟩

section SeamLoc
variable {D : D7} {X : Fields} (s : Seam D X) {n : ℕ}

theorem tr_smul (c : 𝓞 X.E) (x : Sp X.E n) :
    (fun i => s.iE ((c • x) i)) = RingOfIntegers.mapRingEquiv s.iE c • (fun i => s.iE (x i)) := by
  funext i
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
  rfl

theorem mem_lat_iff (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ ∃ x ∈ N, (fun i => s.iE (x i)) = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, N.zero_mem, by funext i; simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, N.add_mem ha hb, by funext i; simp⟩
    | smul r y _ hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • a, N.smul_mem _ ha, ?_⟩
      rw [tr_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem tr_inj : Function.Injective (fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) := by
  intro x y h
  funext i
  exact s.iE.injective (congrFun h i)

theorem mem_localization_lattice_iff (P : HeightOneSpectrum (𝓞 X.E)) (N : Submodule (𝓞 X.E) (Sp X.E n)) (x : Sp X.E n) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ (fun i => s.iE (x i)) ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  constructor
  · rintro ⟨c, hc, hcx⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE c, fun h => hc ((mem_seamP s P c).1 h), ?_⟩
    rw [← tr_smul]
    exact (mem_lat_iff s N _).2 ⟨_, hcx, rfl⟩
  · rintro ⟨d, hd, hdx⟩
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective d
    refine ⟨c, fun h => hd ((mem_seamP s P c).2 h), ?_⟩
    rw [← tr_smul] at hdx
    obtain ⟨x', hx', e⟩ := (mem_lat_iff s N _).1 hdx
    rw [tr_inj s e] at hx'
    exact hx'

theorem seam_locP (P : HeightOneSpectrum (𝓞 X.E)) (N N₁ : Submodule (𝓞 X.E) (Sp X.E n))
    (h : Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N₁) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N)) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N₁ = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  ext x
  rw [mem_localization_lattice_iff s P N₁ x, mem_localization_lattice_iff s P N x, h]

end SeamLoc

theorem loc_compan {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E))
    (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)) (hΛ : Λ.FG) (hΛ₁ : Λ₁.FG)
    (h : Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁) :
    Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) :=
  GlobalTheory.T.localization_unimodularCompanion_eq sp J a Q Λ Λ₁ hΛ hΛ₁ h

theorem loc_latAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (Q : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : Formalism.L2.Col.IsOver v Q)
    {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (h : bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x) :
    Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x₁ Lb) = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x Lb) :=
  GlobalTheory.T.hermitianLocalisation_adelicPointLattice_eq hc Q v hv Lb hfin hspan x x₁ h

theorem latAd_fg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : (latAd x Lb).FG :=
  _root_.GlobalTheory.LatAdFG.latAd_fg_of_full Lb hfin hspan x

theorem phiT_lat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hTie j hj β x x₁ p p₁ hp hp₁ hx P
  have hSS := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1
  have hmem : seamP t.seam P.1 ∈ ssRec t u μ :=
    (mem_ssRec t u μ P.1).2 (by classical rw [hSS]; exact Finset.mem_union_left _ P.2)
  obtain ⟨v, hv⟩ := exists_over (F := D.host.F) (seamP t.seam P.1)
  have hxv := hx v ⟨_, hmem, hv⟩
  refine seam_locP t.seam P.1 _ _ ?_
  rw [hp₁.lat, hp.lat]
  refine localization_eq_of_semilocalization_eq' _ ?_
  unfold latCo
  refine loc_mvL _ _ ?_
  refine loc_compan _ _ _ _ _ _ (latAd_fg _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span _)
    (latAd_fg _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span _) ?_
  exact loc_latAd D.sp.cm _ v hv _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span _ _ hxv

end GlobalTheory.PhiTLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrime
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.TwU.BaseCosetInt

theorem baseCosetRep_integral_after_scaling_at_bad_prime : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl Kc Y cX) (t : Formalism.L2.Ker.KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ) (A : AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (P : SB t μ) (l : Fin (D.R.N (t.m2 + 1))),
    IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β P l) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hP hA β P l
  obtain ⟨⟨c, hc⟩, -⟩ := ((St (t.m2 + 1) (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' 1)
  have hY := hA.chain.2.1 c
  have h3 := GlobalTheory.TopInv.repY_mem t.sel (t.tup μ) (t.cst μ) _ _ hY P
  rw [← (frsF t.sel (t.tup μ) (A.pt _ (cpl_lt t μ).le c) P).apply_symm_apply (_ • _)] at h3
  replace h3 := (GlobalTheory.TopStep.frsF_mem _ P _).1 h3
  rw [map_smul] at h3
  have hint := (mem_localization_standardLattice _ _).1 h3 l
  have hmem : repY (A.yb c) ∈ A.yb c := by
    obtain ⟨y, -, hYe⟩ := hY
    exact Classical.epsilon_spec (p := fun z => z ∈ A.yb c) ⟨y, by rw [hYe]; simp⟩
  have hco := hA.coset c _ hmem P l
  rw [hc] at hco
  generalize (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)) = v at hint hco
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := GlobalTheory.TopInv.qOf_ne P.1
  have hqi : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n) := fun n => by
    simpa using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hint hco
  generalize (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) = e at hint ⊢
  generalize (if P.1 ∈ t.Pr.vGs then 0 else (t.cst μ).M) = e0 at hco
  have key : (qOf P.1 : t.X.E) ^ e * v l = (qOf P.1 : t.X.E) ^ e * A.y0 β P l +
      (qOf P.1 : t.X.E) ^ (e + e0) * (((qOf P.1 : t.X.E) ^ e0)⁻¹ * (v l - A.y0 β P l)) := by
    rw [pow_add]
    field_simp
    ring
  rw [key] at hint
  exact (GlobalTheory.TopInv.intAt_add_iff ((hqi _).mul hco)).1 hint

end GlobalTheory.TwU.BaseCosetInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnSidePropertiesTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.Pdv

theorem colSide_of_choices {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hN : GlobalTheory.Pdv.ColNorm I)
    (hX_eq : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hS : t.S = I.S) (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst)
    (hidx : HEq t.idx I.idx) (hm2 : t.m2 = B.R.m - 2) (hglob : HEq t.glob I.glob) : GlobalTheory.KerJ.ColSide t := by
  have hb := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have kCst : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
      (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S') (cst' : ∀ μ, LocCst X' (rowSG Pr' sel' (tup' μ))),
      X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq cst' I.cst →
      ∀ μ, (cst' μ).sharp = true ∧ (I.rec7 l Z).R.m ≤ (cst' μ).A ∧ 2 * (cst' μ).M ≤ twTopDepth (I.rec7 l Z).R := by
    rintro X' Pr' sel' S' tup' cst' rfl h1 h2 rfl h3 h4
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    obtain rfl := eq_of_heq h3
    obtain rfl := eq_of_heq h4
    intro μ
    have h5 := (hN μ)
    refine ⟨hI.sharp μ, h5.1, ?_⟩
    show 2 * (I.cst μ).M ≤ 4 * B.R.m + 1
    omega
  refine ⟨?fields, ?sel, ?bad, ?chOk, ?chars, ?sharp, ?deep, ?repOne⟩
  case fields => exact hX_eq ▸ hb.1
  case sel =>
    have key : ∀ (X' : Fields) (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)),
        X' = B.fields → HEq sel' I.sel → IsSel X' sel' := by
      rintro X' sel' rfl h
      obtain rfl := eq_of_heq h
      exact hI.sel_ok
    exact key _ _ hX_eq hsel
  case bad =>
    have key : ∀ (X' : Fields) (Pr' : Primes X'), X' = B.fields → HEq Pr' (B.primes X) → ∀ v, Pr'.T v ∈ I.S := by
      rintro X' Pr' rfl h
      obtain rfl := eq_of_heq h
      exact hI.T_mem
    rw [hS]
    refine ⟨fun i => ?_, key _ _ hX_eq hPr, fun _ hl => hI.small_mem hl, hI.two_q_d_mem.2.1⟩
    rw [t.g_rec]
    exact hI.g_mem i
  case chOk =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → Ch'.Ok := by
      rintro X' Pr' Ch' rfl h1 h2
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      exact hI.ch_ok
    exact key _ _ _ hX_eq hPr hCh
  case chars =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m) (glob' : ChGlob X' (I.rec7 l Z).R.m)
        (seam' : Seam (I.rec7 l Z) X'), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → HEq glob' I.glob → HEq seam' (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) →
        ∃ eta, Ch'.Tied glob'.σ₀ (fun j τ => ((I.rec7 l Z).hc (seam'.iT τ)).e j) glob'.mu0 eta := by
      rintro X' Pr' Ch' glob' seam' rfl h1 h2 h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      exact ⟨I.C.eta, hI.ch_tied⟩
    exact key _ _ _ _ _ hX_eq hPr hCh hglob hseam
  case sharp => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).1
  case deep => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).2
  case repOne =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
        (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S')
        (idx' : ∀ μ, ChIdx X' Pr' (I.rec7 l Z).R (QE sel' (tup' μ : Chr X'.F X'.E X'.K))),
        X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq idx' I.idx →
        ∀ μ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (idx' μ).β j) (P : rowSG Pr' sel' (tup' μ)), P.1 ∈ Pr'.vGs → (idx' μ).h j b P = 1 := by
      rintro X' Pr' sel' S' tup' idx' rfl h1 h2 rfl h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      intro μ
      exact (hN μ).2.2
    rw [hm2]
    exact key _ _ _ _ _ _ hX_eq hPr hsel hS htup hidx

theorem colSide_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.KerJ.ColSide t := by
  intro B X I hI _ l Z L hT Gi Gl K Y cX ex t hN hS
  exact colSide_of_choices I hI l Z t hN hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.tup hS.cst hS.idx hS.m2 hS.glob

end GlobalTheory.Pdv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionHermitianLatticeFg
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.CompanFG

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Lb := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMem.exists_smul_mem
  | exact _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem
  | (apply _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem ..)

theorem hform_single {E : Type} [Field E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E)
    (c : E) (i : Fin N) (y : Fin N → E) :
    hform σ J (c • Pi.single i 1) y = σ c * (J *ᵥ y) i := by
  simp [hform, Pi.single_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc, apply_ite σ, ite_mul]

theorem dualSet_le_fg {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E)
    (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (Lb : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    ∃ M : Submodule (𝓞 E) (Fin N → E), M.FG ∧ dualSet σ J Lb ⊆ M := by
  choose c hc0 hcm using fun i : Fin N => exists_smul_mem Lb hsp (Pi.single i 1)
  refine ⟨Submodule.span (𝓞 E) (Set.range fun i => (σ (c i : E))⁻¹ • (J⁻¹ *ᵥ Pi.single i 1)),
    Submodule.fg_span (Set.finite_range _), ?_⟩
  intro y hy
  have hint : ∀ i, ∃ w : 𝓞 E, (w : E) = σ (c i : E) * (J *ᵥ y) i := by
    intro i
    have h := hy _ (hcm i)
    rw [← algebraMap_smul E (c i), hform_single] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨w, hw⟩
  choose w hw using hint
  have hσ : ∀ i, σ (c i : E) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast hc0 i
  have hy' : y = ∑ i, w i • ((σ (c i : E))⁻¹ • (J⁻¹ *ᵥ Pi.single i 1)) := by
    have e1 : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    conv_lhs => rw [e1, ← Finset.univ_sum_single (J *ᵥ y)]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (w i), smul_smul, ← Matrix.mulVec_smul]
    congr 1
    ext k
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · subst_vars
      show (J *ᵥ y) k = (algebraMap (𝓞 E) E (w k)) * (σ (c k : E))⁻¹ * 1
      rw [show algebraMap (𝓞 E) E (w k) = (w k : E) from rfl, hw k]
      field_simp [hσ k]
    · simp
  rw [hy']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanFG

namespace GlobalTheory


open GlobalTheory.CompanFG in
theorem compan_fg {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (a : 𝓞 E)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG) (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    (compan (sp := sp) J a Lb).FG := by
  obtain ⟨M, hM, hle⟩ := dualSet_le_fg (sp.cm.sig : E →+* E) J hJ Lb hsp
  have h1 : (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)).FG :=
    fg_of_le_fg hM (Submodule.span_le.mpr hle)
  exact hfg.sup (fg_of_le_fg h1 Submodule.smul_le_right)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealCharacterClassLatticeEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem chi_detId_lat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => (∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 → ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)) → (∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)) → ∀ i (hi : i ≤ D.R.m) c, t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (t.seam.lat ((t.rd u μ).N i c))) = ((D.chiD ((t.O u μ).dt i c) : ℂˣ) : ℂ)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ _ _ i hi c
  rw [← t.O_lat, t.χ_rec, ← Formalism.L2.Ker.initial_lattice_eq_standard (t.O u μ) i, ← t.idl_ok.2.2.2.2 _ ((t.O u μ).L0 i) ((t.O u μ).lat i c),
    ← (t.O u μ).dt_lat, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
  rfl

end GlobalTheory.TwV
end
end

