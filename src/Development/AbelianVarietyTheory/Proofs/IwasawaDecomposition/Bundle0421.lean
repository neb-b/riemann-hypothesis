module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNatCastEqOne
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem conj_eq_complexConj (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

theorem norm_natCast_eq_one {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) : ‖(k : ℂ_[p])‖ = 1 := by
  rw [GlobalTheory.EigenGenerator.norm_natCast_eq]
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hk)

theorem exists_unitary_at (p : ℕ) (hp : p.Prime) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ G : Matrix (Fin N) (Fin N) D.host.E, (G.map D.host.conj).transpose * G = 1 ∧
      (∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E))) ∧
      (∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram D.sp.cm.cmUnram
  have hsd : (⟨L, hL.1, hL.2.1⟩ : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat D.host.E N).SelfDual := by
    intro x
    have h3 := hL.2.2 x
    refine h3.trans (forall₂_congr fun y _ => ?_)
    have e : stdH D.host.E N y x = GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm x y := by
      unfold stdH GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      rfl
    rw [e]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  obtain ⟨γ, hγ, h1, h2⟩ := GlobalTheory.GenusSelfDual.inGenus_of_selfDual hsd p hp
  refine ⟨LinearMap.toMatrix' γ.toLinearMap, ?_, fun x hx => ?_, fun a => ?_⟩
  · ext a b
    have h := hγ (Pi.single b 1) (Pi.single a 1)
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm (Pi.single b (1 : D.host.E)) (Pi.single a 1) = if a = b then 1 else 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      rw [Finset.sum_eq_single b]
      · by_cases hab : a = b
        · subst hab; simp
        · simp [Pi.single_apply, Ne.symm hab, hab]
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    rw [hr] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply, LinearMap.toMatrix'_apply,
      LinearEquiv.coe_coe, conj_eq_complexConj]
    rw [← h]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · obtain ⟨k, hk, hkx⟩ := h1 x hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hkx
    choose c hc using GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.mem_stdMod.1 hy
    refine ⟨k, hk, c, ?_⟩
    rw [LinearMap.toMatrix'_mulVec, Nat.cast_smul_eq_nsmul]
    rw [← hyx]
    have : (fun a => (c a : D.host.E)) = y := funext hc
    rw [this]
    rfl
  · have hm : (fun i => LinearMap.toMatrix' γ.toLinearMap i a) ∈ ((GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat.std D.host.E N).map γ).L := by
      refine Submodule.mem_map.2 ⟨Pi.single a 1, GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.single_mem_stdMod a, ?_⟩
      funext i
      simp [LinearMap.toMatrix'_apply]
    obtain ⟨k, hk, hkx⟩ := h2 _ hm
    exact ⟨k, hk, by rwa [Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.Mem.Col2.TC.AdaptedBases

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem basR_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (G : Matrix (Fin N) (Fin N) D.host.E) (hdet : G.det ≠ 0)
    (h1 : ∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E)))
    (h2 : ∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) :
    GL3Columns.BasR D lam τ L (G.map (tauEmb D lam τ)) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  unfold GL3Columns.BasR
  rw [hρ]
  have hdet' : (G.map ρ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero ρ).2 hdet
  refine ⟨hdet', fun x hx a => ?_, fun a => ?_⟩
  · obtain ⟨k, hk, c, hc⟩ := h1 x hx
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    have hv : (fun i => ρ (x i)) = (G.map ρ).mulVec ((k : ℂ_[p])⁻¹ • fun a => ρ (c a : D.host.E)) := by
      funext i
      have e := congrArg (fun v => ρ (v i)) hc
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at e
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hk0, e, RingHom.map_mulVec]
      rfl
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet'), Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul, norm_mul, norm_inv, hk1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ (c a)
  · obtain ⟨k, hk, hkL⟩ := h2 a
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    refine ⟨1, fun _ => (k : ℂ_[p])⁻¹, fun _ => (k : D.host.E) • fun i => G i a, fun _ => by rw [norm_inv, hk1, inv_one],
      fun _ => hkL, fun i => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.map_apply]
    rw [inv_mul_cancel_left₀ hk0]

theorem dualM_eq_self {N : ℕ} {G : Matrix (Fin N) (Fin N) D.host.E} (h : (G.map D.host.conj).transpose * G = 1) : dualM G = G :=
  Matrix.inv_eq_right_inv h

theorem basR_smul {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} {N : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M : Matrix (Fin N) (Fin N) ℂ_[p]} (hM : GL3Columns.BasR D lam τ L M)
    {s : ℂ_[p]} (hs : ‖s‖ = 1) : GL3Columns.BasR D lam τ L (s • M) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs; exact zero_ne_one hs
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, fun x hx a => ?_, fun a => ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) h0
  · have e : (s • M)⁻¹ = s⁻¹ • M⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h0)]
    rw [e, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, hs, inv_one, one_mul]
    exact h1 x hx a
  · obtain ⟨n, r, x, hr, hx, he⟩ := h2 a
    refine ⟨n, fun k => s * r k, x, fun k => by rw [norm_mul, hs, one_mul]; exact hr k, hx, fun i => ?_⟩
    rw [Matrix.smul_apply, he i, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem ne_two_ne_q_of_adPl {w : D.what₂.places.Pl} (hw : AdPl D w) :
    D.what₂.places.resChar w ∉ D.host.small ∧ D.what₂.places.resChar w ≠ D.host.q := by
  unfold AdPl Formalism.BasicNotions.Host.cls at hw
  constructor
  · intro h
    simp [Formalism.BasicNotions.primeClass, h] at hw
  · intro h
    rw [h, Formalism.BasicNotions.primeClass_q] at hw
    simp at hw

theorem dgenUnitAd (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : DgenUnitAd P O := by
  intro w hw u μ τ
  obtain ⟨h2, hq⟩ := ne_two_ne_q_of_adPl hw
  obtain ⟨M, hM, hemb, hs⟩ := (O u μ).dgen_gen
  obtain ⟨s, hs1, hs2⟩ := hs τ
  rw [← hs1]
  exact GlobalTheory.EigenGenerator.norm_generator_eq_one D _ (P.lam w) h2 hq M hemb τ s hs2

theorem exists_sys (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (u : D.what₂.Word)
    (μ : D.what₂.Tup) : ∃ Pm : SysFam D u μ,
      (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) := by
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  choose G hG h1 h2 using fun i (c : (D.chTw u μ).cls i) =>
    exists_unitary_at (D := D) (D.what₂.places.resChar w) hp ((O u μ).lat i c).1 ((O u μ).lat i c).2
  refine ⟨fun i c _ => G i c, fun i _ c τ => ?_, fun _ _ _ _ _ _ => rfl, fun i _ c _ _ _ => (dualM_eq_self (hG i c)).symm⟩
  exact basR_of (P.lam w) τ _ (G i c) (Matrix.det_ne_zero_of_left_inverse (hG i c)) (h1 i c) (h2 i c)

end GlobalTheory.Mem.Col2.TC.AdaptedBases

open IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Lift

def sgnGL (n : ℕ) (S : Type) [CommRing S] (ε : ℤˣ) : GL (Fin n) S := Units.map (Int.castRingHom _).toMonoidHom ε

theorem sgnGL_val (n : ℕ) (S : Type) [CommRing S] (ε : ℤˣ) : (sgnGL n S ε).1 = (ε : ℤ) • 1 := (zsmul_one _).symm

theorem sgnGL_comm {n : ℕ} {S : Type} [CommRing S] (ε : ℤˣ) (x : GL (Fin n) S) : x * sgnGL n S ε = sgnGL n S ε * x :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, sgnGL_val, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])

theorem bc_sgnGL {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (ε : ℤˣ) :
    Formalism.UG.bc f (sgnGL n S ε) = sgnGL n S' ε :=
  Units.ext (map_intCast (f.mapMatrix : Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) S') (ε : ℤ))

theorem map_sgn {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (ε : ℤˣ) (i j : Fin n) :
    (sgnGL n S' ε).1 i j = f ((sgnGL n S ε).1 i j) := by
  rw [← bc_sgnGL f]; rfl

theorem frGL_sgn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (ε : ℤˣ) : frGL β (sgnGL n _ ε) = sgnGL n _ ε := by
  have h : intGL F E n (sgnGL n _ ε) = sgnGL n _ ε := bc_sgnGL (Formalism.L2.Herm.intAf F E).subtype ε
  rw [frGL, MonoidHom.comp_apply, h, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, sgnGL_comm, mul_inv_cancel_right]

theorem exists_matrix_sign {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (ε : ℤˣ)
    (h : ∀ P ∈ T, redFn β P x = sgnGL n _ ε) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - (sgnGL n _ ε).1) = M • N :=
  GlobalTheory.LevelUnique.exists_matrix_hat hfr T hJ hx ⟨sgnGL n _ ε, rfl⟩
    (fun P hP => by rw [h P hP, redFn_frGL, bc_sgnGL]) hb hK
    (fun i j => by
      rw [frGL_sgn]
      exact map_sgn (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom ε i j)

theorem eq_sgn_of_submatrix {n r : ℕ} (hr : n = r) (h : r ≤ n) {S : Type} [CommRing S] {x : GL (Fin n) S} {ε : ℤˣ}
    (e : x.1.submatrix (Fin.castLE h) (Fin.castLE h) = (sgnGL r S ε).1) : x = sgnGL n S ε := by
  subst hr
  exact Units.ext e

theorem sign_calc {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {x z w₂ w₃ : Fin n → R} {M : ℕ} {ε : ℤˣ}
    (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - (sgnGL n R ε).1 *ᵥ z = M • w₃) : x - (ε : ℤ) • z = M • (w₂ + w₃) := by
  rw [smul_add, ← e₂, ← e₃, sub_add_sub_cancel, sgnGL_val, Matrix.smul_mulVec, Matrix.one_mulVec]

variable {D : D7}

theorem finVec_sub_zsmul (V : HSp D) (x y : Fin V.rank → D.host.E) (e : ℤ) :
    finVec V (x - e • y) = finVec V x - e • finVec V y := by
  funext j
  exact (map_sub (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) (x j) (e • y j)).trans
    (congrArg (fun t => finVec V x j - t) (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) e (y j)))

theorem hatV_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) : GlobalTheory.Ker.hatV Λ = Formalism.L2.Pj.latHat V := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  rw [hl]; rfl

theorem mulVec_mem {V : HSp D} {k : GA D V} (hk : GlobalTheory.Member.FinCong V 1 k) :
    ∀ z ∈ Formalism.L2.Pj.latHat V, (finHom V k).1 *ᵥ z ∈ Formalism.L2.Pj.latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [one_nsmul] at e
  rw [sub_eq_iff_eq_add.1 e]
  exact add_mem hy hz

theorem isMov_of_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {k : GA D V} (hk : Lev.finE V k ∈ St β) : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) Λ Λ := by
  have hk' : Lev.finE V k⁻¹ ∈ St β := by rw [map_inv]; exact inv_mem hk
  have h1 := mulVec_mem (GlobalTheory.LevelAction.finCong_of_mem_St hβ hk)
  have h2 := mulVec_mem (GlobalTheory.LevelAction.finCong_of_mem_St hβ hk')
  intro u
  rw [hatV_eq hβ]
  change _ ↔ ∃ u₀ ∈ _, u = (finHom V k).1 *ᵥ u₀
  constructor
  · intro hu
    exact ⟨_, h2 u hu, by rw [← GlobalTheory.Member.LatMove.fin_mul, mul_inv_cancel, GlobalTheory.Member.LatMove.fin_one]⟩
  · rintro ⟨u₀, h0, rfl⟩
    exact h1 u₀ h0

theorem cong_on_half {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    {K K' : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ b ∈ J, ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • (K *ᵥ z - K' *ᵥ z) = M • w) :
    ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      K *ᵥ finVec V (ι a) - K' *ᵥ finVec V (ι a) = M • w := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  intro a ha
  refine Submodule.smul_induction_on ha (fun b hb a _ => ?_) ?_
  · obtain ⟨w, hw, e⟩ := h b hb _ ((GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hm a))
    have e₀ : finVec V (ι (b • a)) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • finVec V (ι a) := by
      rw [map_smul]; exact GlobalTheory.AdLat.Tower.fv_smul b (ι a)
    exact ⟨w, hw, by rw [e₀, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, e]⟩
  · rintro x y ⟨w, hw, e⟩ ⟨w', hw', e'⟩
    have e₀ : finVec V (ι (x + y)) = finVec V (ι x) + finVec V (ι y) := by
      rw [map_add (f := _)]; funext i; exact TensorProduct.tmul_add _ _ _
    refine ⟨w + w', add_mem hw hw', ?_⟩
    rw [e₀, Matrix.mulVec_add, Matrix.mulVec_add, smul_add, ← e, ← e']
    abel

theorem mark_calc {R : Type} [CommRing R] {n : ℕ} {Hm K K' : Matrix (Fin n) (Fin n) R} {m x z w₁ w₂ w₃ : Fin n → R} {M : ℕ}
    (e₁ : m - Hm *ᵥ x = M • w₁) (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - K' *ᵥ z = M • w₃) :
    m - Hm *ᵥ (K' *ᵥ z) = M • (w₁ + Hm *ᵥ (w₂ + w₃)) := by
  rw [smul_add, ← Matrix.mulVec_smul, smul_add, ← e₁, ← e₂, ← e₃, sub_add_sub_cancel, Matrix.mulVec_sub, sub_add_sub_cancel]

theorem exists_cong_sign {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) (ε : ℤˣ)
    (h : ∀ P ∈ T, redFn β P (Lev.finE V k) = sgnGL _ _ ε) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z -
        (sgnGL V.rank (Af D.host.F ⊗[D.host.F] D.host.E) ε).1 *ᵥ z) = M • w := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := (hatV_eq hβ).symm
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_sign hfr T hJ hk ε h hb (K := (finHom V k).1) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem redFn_sign {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k : GA D V} (hk : Lev.IsLevelLift V β L g k) (ε : ℤˣ) (hg : ∀ P, g P = sgnGL _ _ ε) :
    ∀ P ∈ L.Pg, redFn β P (Lev.finE V k) = sgnGL _ _ ε := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = g ⟨P, hP⟩ := congrFun hk.2.2 ⟨P, hP⟩
  have e' := congrArg Units.val (e.trans (hg ⟨P, hP⟩))
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP))] at e'
  exact eq_sgn_of_submatrix hr L.hr e'

theorem exists_div {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {a : La}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1) (e : finVec V (ι a) = M • w) :
    ∃ b, a = M • b := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have h5 := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  obtain ⟨⟨v, hv⟩, ev⟩ := GlobalTheory.AdLat.Tower.exists_div (F := D.host.F) (M := latG V 1)
    (fun v => h5 ▸ (GlobalTheory.Member.LatMove.mem_lat_iff V 1 v).symm) hM ⟨_, hm a⟩ (h5 ▸ hw) e
  obtain ⟨c, rfl⟩ : v ∈ LinearMap.range ι := hι.2 ▸ hv
  refine ⟨c, hι.1 ?_⟩
  rw [map_nsmul]
  exact congrArg Subtype.val ev

theorem sign_div {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {a a' : La} {e : ℤ}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1)
    (h : finVec V (ι a') - e • finVec V (ι a) = M • w) : ∃ b, a' = e • a + M • b := by
  obtain ⟨b, hb⟩ := exists_div (a := a' - e • a) hι hM hw (by rw [map_sub, map_zsmul, finVec_sub_zsmul, h])
  exact ⟨b, by rw [← hb, add_sub_cancel]⟩

theorem mu_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) {k : GA D W}
    {x : (AE D)ˣ} (hx : IsDetRoot W k x) : castDict hV mu k = ((χ x : Circle) : ℂ) := by
  subst hV
  exact h.2 k x hx

theorem mem_iff_prod_le {E : Type} [Field E] [NumberField E] (T : Finset (Pl E)) (P : Pl E) :
    P ∈ T ↔ ∏ Q ∈ T, Q.asIdeal ≤ P.asIdeal := by
  rw [P.isPrime.prod_le]
  refine ⟨fun h => ⟨P, h, le_rfl⟩, ?_⟩
  rintro ⟨Q, hQ, h⟩
  rwa [← HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)]

end GlobalTheory.OneMapRef.Lift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedGLEqOneOfLqPrinc
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
open Formalism.MainNotions Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Col2.TopCh
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopStepPrimes

open IsDedekindDomain.HeightOneSpectrum GlobalTheory.TopStep

theorem reduction_eq_zero_of_valuation_le {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {x : E}
    (h : P.valuation E x ≤ WithZero.coe (Multiplicative.ofAdd (-((1 : ℕ) : ℤ)))) : redP P x = 0 := by
  have hlt : P.valuation E x < 1 := h.trans_lt (by decide)
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer x hlt.le
  have hd : (d : 𝓞 E) ∉ P.asIdeal := d.2
  have hdv : P.valuation E (algebraMap (𝓞 E) E d) = 1 := by
    rw [valuation_of_algebraMap]
    exact le_antisymm (P.intValuation_le_one _) (not_lt.1 fun hc => hd ((P.intValuation_lt_one_iff_mem _).1 hc))
  have hn : n ∈ P.asIdeal := by
    rw [← P.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E n) < 1
    rw [← hnd, map_mul, hdv, mul_one]
    exact hlt
  have hs := reduction_spec P hd (a := x) (r := n) (by rw [mul_comm]; exact hnd)
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hn] at hs
  exact (mul_eq_zero.1 hs).resolve_left (mk_ne_zero hd)

theorem redGL_eq_one_of_lqPrinc {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (g : GLint E n P) (hg : lqPrinc P 1 (g : Sp E n ≃ₗ[E] Sp E n)) : redGL n P g = 1 := by
  apply Units.ext
  rw [redGL_val]
  ext i j
  have h2 : LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) i j = g.1 (Pi.single j 1) i := by
    rw [LinearMap.toMatrix'_apply]
    rfl
  have hv := hg i j
  rw [Matrix.sub_apply, h2] at hv
  have hx := glint_entry g i j
  have hδ : IntAt P ((1 : Matrix (Fin n) (Fin n) E) i j) := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using intAt_one
    · simpa [Matrix.one_apply, hij] using intAt_zero
  have hr : redP P ((1 : Matrix (Fin n) (Fin n) E) i j) = (1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using reduction_one₂
    · simpa [Matrix.one_apply, hij] using reduction_zero
  have e : g.1 (Pi.single j 1) i = (g.1 (Pi.single j 1) i - (1 : Matrix (Fin n) (Fin n) E) i j) +
      (1 : Matrix (Fin n) (Fin n) E) i j := by ring
  show redP P (g.1 (Pi.single j 1) i) = _
  rw [e, reduction_add (intAt_sub hx hδ) hδ, reduction_eq_zero_of_valuation_le hv, zero_add, hr]
  rfl

end GlobalTheory.TopStepPrimes


open GlobalTheory.TopStepPrimes in
theorem GlobalTheory.TopStepPrimes.primes_top_ok : ∀ {B : Base} {X : PreX B.toPre} {I : TC B X}, I.Ok → ∀ (u : B.Word) (a : I.ι), Disjoint (B.primes X).vGs (I.Q a) ∧ (∀ P ∈ uSG ∅ (uSG (B.primes X).vGs (I.Q a)), conjPrime₂ P ∉ uSG ∅ (uSG (B.primes X).vGs (I.Q a))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.fields.E (B.R.N B.R.m - 1) P.1)), lqPrinc P.1 1 (g : Sp B.fields.E (B.R.N B.R.m - 1) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m - 1)) → ∃ h : g ∈ (levQX B.R I.sel (I.tup a) P).H, (levQX B.R I.sel (I.tup a) P).lam ⟨g, h⟩ = 1 := by
  intro B X I h u a
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.Mem.LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)
  · intro P hP
    have h1 := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    unfold Sall at h1
    simp only [Finset.mem_union] at h1 hP ⊢
    rcases hP with h0 | hP
    · exact absurd h0 (Finset.notMem_empty _)
    · rintro (hc | hc)
      · exact Finset.notMem_empty _ hc
      · exact (h1 P (Or.inr hP)).1 (Or.inr hc)
  · intro P g hg
    have e := redGL_eq_one_of_lqPrinc g hg
    refine ⟨(mem_levQX _ _ _ _).2 (e ▸ Subgroup.one_mem _), ?_⟩
    rw [levQX_lam]
    have key : ∀ {G M : Type} [Group G] [Monoid M] (H : Subgroup G) (f : H →* M) (y : G) (hy : y ∈ H), y = 1 → f ⟨y, hy⟩ = 1 := by
      rintro G M _ _ H f y hy rfl
      exact map_one f
    exact key _ _ _ _ e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesReferenceTupleEqEmpty
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.RefTup

theorem qe_one_tup {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem twistPrimes_reference_tuple_eq_empty : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Q I.mu0 = ∅ := by
  intro B X I
  show QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅
  rw [I.trueColumn_tuple_trivial_eq_one]
  exact qe_one_tup I.sel

end GlobalTheory.Mem.Col2.RefTup
end

