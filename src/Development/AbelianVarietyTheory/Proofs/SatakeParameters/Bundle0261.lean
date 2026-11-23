module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousToZModComp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatAtRep
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU

theorem latBack_seam_lat {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    latBack s (s.lat N) = N := by
  first
  | exact @_root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat
  | exact _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat
  | (apply _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat ..)

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixOneAtPlaceScaledPreservesCompletedLaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrix_one_at_place_scaled_preserves_completedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) k = 1 →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Lb,
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) •
        ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  first | exact @GlobalTheory.AwayScale.main | exact GlobalTheory.AwayScale.main | (intros; apply GlobalTheory.AwayScale.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsSameBadComponentsSameLocalizationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoints_same_badComponents_same_localization : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  first | exact @GlobalTheory.PhiTLat.phiT_lat | exact GlobalTheory.PhiTLat.phiT_lat | (intros; apply GlobalTheory.PhiTLat.phiT_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrimeStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl Kc Y cX) (t : Formalism.L2.Ker.KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ) (A : AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (P : SB t μ) (l : Fin (D.R.N (t.m2 + 1))),
    IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β P l) := by
  first | exact @GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime | exact GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime | (intros; apply GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepresentativeBoundedAtBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU

theorem repY_yb_coset_bdd {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (c : (D.chTw u μ).cls (t.m2 + 1)) (P : SB t μ) :
    SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)))
        (A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) P) ∧
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M)) *
        (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)) l) := by
  obtain ⟨w, hw1, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  have hmem : repY (A.yb c) ∈ A.yb c := Classical.epsilon_spec (p := fun y => y ∈ A.yb c) ⟨w, hwm⟩
  refine ⟨H.coset c _ hmem P, ?_⟩
  have hd := (Set.ext_iff.1 hw (repY (A.yb c))).1 hmem
  rw [Set.mem_setOf_eq] at hd
  have h0 := (Submodule.mem_iInf _).1 hd P
  have h1 := (Submodule.mem_iInf _).1 hw1 P
  rw [Submodule.mem_comap] at h0 h1
  have hf := GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)
  set fr := frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) with hfr
  have toStd : ∀ v, v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.pt (t.m2 + 1) (cpl_lt t μ).le c).deco.1.N → ∀ l, IntAt P.1 ((fr P).symm v l) := by
    intro v hv
    refine GlobalTheory.TopStep.mem_stdAt.1 ((hf P _).1 ?_)
    rwa [LinearEquiv.apply_symm_apply]
  have k0 := toStd _ h0
  have k1 := toStd _ h1
  simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at k0 k1
  intro l
  have hq : (qOf P.1 : t.X.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ipow : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n) := fun n => by
    simpa using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)
  have a0 := k0 l
  have a1 := k1 l
  by_cases hP : P.1 ∈ t.Pr.vGs
  · simp only [hP, if_true] at a0 a1 ⊢
    have e : (qOf P.1 : t.X.E) ^ 1 * (fr P).symm (repY (A.yb c)) l =
        (qOf P.1 : t.X.E) ^ 1 * (((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l - ((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm w l) +
          ((qOf P.1 : t.X.E) ^ (-1 : ℤ))⁻¹ * (fr P).symm w l := by
      simp only [zpow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, pow_one]
      ring
    rw [e]
    exact IntAt.add (IntAt.mul (ipow 1) a0) a1
  · simp only [hP, if_false] at a0 a1 ⊢
    have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * (fr P).symm (repY (A.yb c)) l =
        (qOf P.1 : t.X.E) ^ (2 * (t.cst μ).M) * (((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l -
          ((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm w l) +
          ((qOf P.1 : t.X.E) ^ (-((t.cst μ).M : ℤ)))⁻¹ * (fr P).symm w l := by
      simp only [_root_.zpow_neg, inv_inv, zpow_natCast]
      field_simp
      ring
    rw [e]
    exact IntAt.add (IntAt.mul (ipow _) a0) a1

theorem baseCosetRepresentative_bounded_at_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))), IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H β x Q l
  obtain ⟨⟨c, hc⟩, -⟩ := ((St _ (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' x)
  subst hc
  obtain ⟨hs, hb⟩ := repY_yb_coset_bdd H c Q
  set w := (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) Q).symm (repY (A.yb c)) with hw
  have hsl := hs l
  have hbl := hb l
  simp only [Pi.sub_apply] at hsl
  have hq : (qOf Q.1 : t.X.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => Q.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ineg : ∀ n : ℕ, IntAt Q.1 (-((qOf Q.1 : t.X.E) ^ n)) := fun n => by
    simpa using IntAt.coe Q.1 (-((qOf Q.1 : 𝓞 t.X.E) ^ n))
  by_cases hP : Q.1 ∈ t.Pr.vGs
  · simp only [hP, if_true] at hsl hbl ⊢
    have e : (qOf Q.1 : t.X.E) ^ 1 * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l =
        (qOf Q.1 : t.X.E) ^ 1 * w l + (-((qOf Q.1 : t.X.E) ^ 1)) *
          (((qOf Q.1 : t.X.E) ^ 0)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l)) := by
      simp only [pow_zero, inv_one, one_mul]
      ring
    rw [e]
    exact IntAt.add hbl (IntAt.mul (ineg 1) hsl)
  · simp only [hP, if_false] at hsl hbl ⊢
    have e : (qOf Q.1 : t.X.E) ^ (t.cst μ).M * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l =
        (qOf Q.1 : t.X.E) ^ (t.cst μ).M * w l + (-((qOf Q.1 : t.X.E) ^ (2 * (t.cst μ).M))) *
          (((qOf Q.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l)) := by
      field_simp
      ring
    rw [e]
    exact IntAt.add hbl (IntAt.mul (ineg _) hsl)

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTarget
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem gmap_of_fix {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {Λ : LevFam X.E X.K n SG}
    {Θ : LevQFam X.E X.K n Q} (a : FrmG Λ Θ) (p : DecoF X.E n ST SG Q) (h : a • p = p) :
    gmap a.1.1 p.deco.1.N = p.deco.1.N :=
  congrArg (fun q : DecoF X.E n ST SG Q => q.deco.1.N) h

theorem mulLat_mul_le {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (a b : ℕ)
    (M : Submodule (𝓞 E) H) : mulLat (a * b) M ≤ mulLat b M := by
  rintro z ⟨w, hw, rfl⟩
  refine ⟨((a : 𝓞 E)) • w, M.smul_mem _ hw, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Nat.cast_mul, mul_comm]

theorem term_law : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → ∀ u μ (G : StabDat (D.chTw u μ)), StabPin t u μ G → ∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw (t.O u μ) i c c' g := by
  intro D L hT Gi Gl K Y cX ex t hC u μ G hG i hi c c' g hg
  have hok := t.idx_ok μ
  have hm := hok.hm
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  obtain ⟨pt, ix, yb, pT, hN, hyb, hE, hC1, hTop, hGi, hGm, hGT⟩ := hG
  have dat := _root_.GlobalTheory.KFiDat.termLaw_of_xi D L hT Gi Gl K Y cX ex t hC.fields hC.sel hC.bad.1 hC.bad.2.1 hC.bad.2.2.1 hC.bad.2.2.2 hC.chars u μ i hi c c'
  have fin : ∀ (f : HomE t.X.E (D.R.N i) (D.R.N (i + 1)) → t.X.K) (N : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)))
      (N' : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N (i + 1)))) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K),
      (t.rd u μ).N i c = N → (t.rd u μ).N (i + 1) c' = N' → (∀ x, (t.rd u μ).Xi i c c' x = t.seam.σ₀ (f x)) →
      gmap γ.1 N' = N' →
      (∀ x z, z ∈ mulLat (cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) (homAt (Sall t.sel (t.tup μ) (t.word u)) N N') → f (x + z) = f x) →
      (∀ x, f (γ.1.toLinearMap ∘ₗ x) * ∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) = k * f x) →
      TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
    intro f N N' γ k hN1 hN2 hf hγ hinv hlaw
    subst hN1 hN2
    refine dat γ k hγ (fun x z hz => ?_) fun x => ?_
    · rw [hlev, hSS] at hz
      rw [hf, hf, hinv x z (mulLat_mul_le _ _ _ hz)]
    · rw [hf, hf, ← map_mul, ← map_mul, hlaw]
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · rw [hGi (i + 1) (by omega) (by omega) c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN i (by omega) c) (hN (i + 1) (by omega) c') (hE i hlt c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiEntry_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok i hlt _ _ _ _ x z hz)
      (GlobalTheory.FiLaw.xiEntry_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) i hlt _ _ _ _ a hfix)
  · subst heq
    obtain ⟨b, -⟩ := hok.last_uniq
    rw [hGm b c'] at hg
    obtain ⟨a, hfix, hY, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ (Nat.le_succ _) c) (hN _ le_rfl c') (hC1 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiCpl1_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok _ _ _ _ x z hz)
      (GlobalTheory.StabLaw.xiCpl1_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob _ hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) _ b _ _ _ a (hyb c') hfix hY)
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    rw [hGT c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ le_rfl c) (hTop.1 c') (hTop.2 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => GlobalTheory.T.lastStep_datum_invariant_cB_hom_twist_primes t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok
        (t.word u) _ _ _ x z (hyb c) hz)
      (GlobalTheory.T.lastStepDatum_law_topLevelStabilizer t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (hC.deep μ).2 (t.word u) _ _ _ a (hyb c) hfix)

end GlobalTheory.KerJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionHermitianLatticeFgStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionHermitianLattice_fg : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → (compan (sp := sp) J a Lb).FG := by
  first | exact @GlobalTheory.compan_fg | exact GlobalTheory.compan_fg | (intros; apply GlobalTheory.compan_fg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexCoordinatesColumnFieldIdentificationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCoordinates_columnFieldIdentification : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (δ : ℂ) {a b : ℕ}, Function.Bijective (seamHom s (a := a) (b := b)) ∧ (∀ x : HomE D.host.E a b, embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ)) ∧ (∀ (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ v : VV D.what₂.Tau a b, (fun τ => v (s.iT τ)) ∈ laV (X.embC s.σ₀) δ M ↔ v ∈ laV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ M') ∧ (δ ≠ 0 → ∀ (Ξ : HomE X.E a b → ℂ) (v : VV D.what₂.Tau a b), onV (X.embC s.σ₀) δ Ξ (fun τ => v (s.iT τ)) = onV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) v) := by
  first | exact @GlobalTheory.TwU.SeamEmb.seam_coords | exact GlobalTheory.TwU.SeamEmb.seam_coords | (intros; apply GlobalTheory.TwU.SeamEmb.seam_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelLevelCharEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LevOne

theorem cong_mem_level_chr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hCh hsel hL j hj b P k hk
  classical
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 (cst.D P) k (hL.cst_ok.D_pos P) hk
  set κ : GLint X.E (R.N j) P.1 := ⟨k, hkG⟩ with hκdef
  have hψ : cst.psi P (Loc.n1Arg (GlobalTheory.CongLevel.extE (cOf R j) k)) = 1 := by
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords]
    exact hL.cst_ok.psi_int P 0 (by simpa using GlobalTheory.CongLevel.intAt_nat P.1 0)
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  by_cases hP : P.1 ∈ Pr.vGs
  · have hD1 : cst.D P = 1 := hL.depthG P hP
    have hdu := GlobalTheory.Mem.Col2.degOneUnram_of_mem_vGs hX.ok hPr hP
    have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) :=
      fun a ha h0 => GlobalTheory.TopStep.intAt_div_of_redP hdu.2 ha h0
    have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (k x) = redV P.1 x := by
      have h1 := GlobalTheory.TopStep.redGL_of_prinCong (by omega : 0 < cst.D P) hkC
      intro x hx
      have h2 := GlobalTheory.TopStep.redV_redGL κ hx
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have hh := hL.stabG j b P hP
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe cst.sharp j P.1 hP hd (L.h j b P) hh k hkG hred, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    have hh' := hh
    unfold lamYat at hh'
    rw [if_pos hP] at hh'
    have hcong := GlobalTheory.CongLevel.conj_cong (qOf P.1) _ _ (L.h j b P) hh'
      (GlobalTheory.CongLevel.extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd k hkG hred)
    have h1 := GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one Ch mu cst.sharp j P.1 hP ((qOf P.1 : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have hx' := hx
        unfold lamYat at hx' ⊢
        rw [if_pos hP] at hx' ⊢
        have h2 := hcong x hx'
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, hψ, inv_one, one_mul]
  · have hstd : ∀ x, x ∈ lamYat (Pr := Pr) (R := R) j P.1 ↔ x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro x
      unfold lamYat
      rw [if_neg hP]
      unfold LocE.lamY
      rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
      simp only [LocE.scE, Pi.zero_apply, Nat.cast_zero, ite_self, zpow_zero, inv_one, one_mul]
    have hbd := hL.boundQ j b P hP
    have hbd' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
        ((qOf P.1 : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := fun x hx => by
      have h1 := hbd x ((hstd x).2 hx)
      exact ⟨(hstd _).1 h1.1, (hstd _).1 h1.2⟩
    have hjD : j + 1 ≤ cst.D P := by
      have h1 := hL.depthQ' P hP
      have h2 := hL.hm
      omega
    have hg := _root_.GlobalTheory.QCong.conj_extE_cong P.1 (cOf R j) j (cst.D P) (L.h j b P) κ hkC hjD hbd'
    have hginv := _root_.GlobalTheory.QCong.conj_extE_cong P.1 (cOf R j) j (cst.D P) (L.h j b P) κ⁻¹ (inv_mem hkC) hjD hbd'
    have einv : ((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) (κ⁻¹).1 * L.h j b P := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, GlobalTheory.CongLevel.extE_inv, mul_assoc]
      rfl
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ k, ?_⟩, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) =
          (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P := by simp
      show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) ∈ Jat (Pr := Pr) cst.sharp j P.1
      rw [e]
      unfold Jat
      rw [if_neg hP]
      refine _root_.GlobalTheory.ParahoricOfCong.mem_JQ_of_cong P.1 (R.k + j) (R.N j) (cOf R j) _ hg ?_
      rw [einv]
      exact hginv
    · unfold chiInv
      rw [hψ, inv_one, one_mul]
      unfold lamRow
      rw [if_neg hP]
      exact _root_.GlobalTheory.LamQBCong.lamQB_eq_one_of_cong P.1 _ (R.k + j) (R.N j) (R.N j + cOf R j) _ (by omega) hg

end GlobalTheory.LevOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumJetsTranslate
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets.Transl

open GlobalTheory.LiftTypePrime GlobalTheory.MomT.PtMoments

theorem exists_denom {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module (𝓞 E) W] {p : ℕ} (hp : p.Prime)
    {M M' : Submodule (𝓞 E) W} (hM : M.FG)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → M ≤ localization₂ P.asIdeal M') :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ M, (s : 𝓞 E) • x ∈ M' := by
  have key : ∀ x : W, ∃ s : ℕ, Nat.Coprime s p ∧ (x ∈ M → (s : 𝓞 E) • x ∈ M') := fun x => by
    by_cases hx : x ∈ M
    swap
    · exact ⟨1, by simp, fun h => absurd h hx⟩
    by_contra hn
    let I : Ideal (𝓞 E) := M'.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
    have hI : I.comap (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(p : ℤ)} := fun z hz => by
      rw [Ideal.mem_span_singleton, Int.natCast_dvd]
      by_contra hz'
      refine hn ⟨z.natAbs, ((Nat.Prime.coprime_iff_not_dvd hp).2 hz').symm, fun _ => ?_⟩
      have hz1 : (z : 𝓞 E) • x ∈ M' := hz
      rcases Int.natAbs_eq z with h1 | h1
      · rw [h1, Int.cast_natCast] at hz1; exact hz1
      · rw [h1, Int.cast_neg, Int.cast_natCast, neg_smul, neg_mem_iff] at hz1; exact hz1
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)}) I hI
    have hpQ : (p : 𝓞 E) ∈ Q := by
      have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
        change (p : ℤ) ∈ Ideal.under ℤ Q
        rw [hQc]
        exact Ideal.mem_span_singleton_self _
      simpa using this
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hp.ne_zero (by simpa using hpQ)
    obtain ⟨c, hc, hcx⟩ : ∃ c : 𝓞 E, c ∉ Q ∧ c • x ∈ M' := h ⟨Q, hQp, hQ0⟩ hpQ hx
    exact hc (hQ hcx)
  choose f hf hfx using key
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∏ x ∈ S, f x, Nat.Coprime.prod_left fun x _ => hf x, fun x hx => ?_⟩
  refine (Submodule.span_le (p := M'.comap (((∏ x ∈ S, f x : ℕ) : 𝓞 E) • LinearMap.id))).2 (fun y hy => ?_) hx
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hy)
  change ((∏ x ∈ S, f x : ℕ) : 𝓞 E) • y ∈ M'
  rw [hc, mul_comm, Nat.cast_mul, mul_smul]
  exact M'.smul_mem _ (hfx y (Submodule.subset_span hy))

theorem stdLat_fg (E : Type) [Field E] (n : ℕ) : (Formalism.L2.Col.stdLat E n).FG :=
  Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _

theorem stdAt_of_stdOver (D : D7) {p : ℕ} (hp : p.Prime) {n : ℕ} {N : Submodule (𝓞 D.host.E) (Sp D.host.E n)} (hN : N.FG)
    (h : StdOver p N) : StdAt D p ((recSeam D).lat N) := by
  obtain ⟨s, hs, h1⟩ := exists_denom hp hN (M' := Formalism.L2.Col.stdLat D.host.E n) fun P hP => (le_locP _ _).trans (h P hP).le
  obtain ⟨t, ht, h2⟩ := exists_denom hp (stdLat_fg D.host.E n) (M' := N) fun P hP => (le_locP _ _).trans (h P hP).ge
  have hl : ∀ x, x ∈ (recSeam D).lat N ↔ x ∈ N := fun x => GlobalTheory.SeamTransport.mem_lat (recSeam D) N x
  refine ⟨Formalism.L2.Col.stdLat D.host.E n, fun x => ?_, s * t, hs.mul_left ht, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun hy => ⟨⟨_, hy⟩, rfl⟩⟩
  · have := h1 x ((hl x).1 hx)
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [mul_comm, mul_smul]
    exact nsmul_mem this _
  · have := h2 x hx
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [hl, mul_smul]
    exact nsmul_mem this _

variable {D : D7} {a b : ℕ}

end GlobalTheory.DatumJets.Transl
end
end

