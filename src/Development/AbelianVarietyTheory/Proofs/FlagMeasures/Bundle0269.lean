module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstA
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryLatticesOfLevel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryOfSelfDualAtPlace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegral
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGlue

open IsDedekindDomain

theorem exists_pow_sat {R : Type*} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R)
    {g : R} (hg : g ≠ 0) :
    ∃ e : ℕ, ∀ x ∈ P.asIdeal ^ e, ∃ s : R, s ∉ P.asIdeal ∧ s * x ∈ Ideal.span {g} := by
  classical
  haveI := P.isPrime
  let Rp := Localization.AtPrime P.asIdeal
  haveI : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot Rp
  have hinj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp P.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  have hI : Ideal.map (algebraMap R Rp) (Ideal.span {g}) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ hinj).2 hg
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨n, fun x hx => ?_⟩
  have hmap : Ideal.map (algebraMap R Rp) (P.asIdeal ^ n) =
      Ideal.map (algebraMap R Rp) (Ideal.span {g}) := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, hn]
  have hx' : algebraMap R Rp x ∈ Ideal.map (algebraMap R Rp) (Ideal.span {g}) :=
    hmap ▸ Ideal.mem_map_of_mem _ hx
  obtain ⟨⟨a, s⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl Rp).1 hx'
  refine ⟨s, s.2, ?_⟩
  have h2 : s.1 * x = a.1 := hinj (by rw [map_mul, mul_comm]; exact h)
  rw [h2]; exact a.2

end GlobalTheory.FrameGlue

open IsDedekindDomain in
theorem GlobalTheory.FrameGlue.glue : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ), 0 < g → ∀ (f f' : Fin (r + 1) → S.V), (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, f a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, f' b - frameAct f ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ))) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, ModG S Λ g (f' b - frameAct f ξ b) := by
  intro E _ _ _ S r Λ g hg f f' hf hloc
  classical
  have hg0 : ((g : 𝓞 E)) ≠ 0 := by exact_mod_cast hg.ne'
  have hfin : {P : HeightOneSpectrum (𝓞 E) | (g : 𝓞 E) ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(g : 𝓞 E)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg0
    · intro P hP
      exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hP)
  choose e he using fun P : HeightOneSpectrum (𝓞 E) => GlobalTheory.FrameGlue.exists_pow_sat P hg0
  let ξP : HeightOneSpectrum (𝓞 E) → Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun P =>
    if h : (g : 𝓞 E) ∈ P.asIdeal then Classical.choose (hloc P h) else 0
  have hξP : ∀ P (h : (g : 𝓞 E) ∈ P.asIdeal), ξP P = Classical.choose (hloc P h) := by
    intro P h; simp only [ξP, dif_pos h]
  have hcrt : ∀ a b : Fin (r + 1), ∃ y : 𝓞 E, ∀ P (hP : P ∈ hfin.toFinset),
      y - ξP P a b ∈ P.asIdeal ^ e P := by
    intro a b
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
      (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) e
      (fun P _ => P.prime) (fun P _ Q _ hPQ => fun h => hPQ (HeightOneSpectrum.ext h))
      (fun P => ξP P.1 a b)
    exact ⟨y, fun P hP => hy P hP⟩
  choose y hy using hcrt
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun a b =>
    if b < a then 0 else if a = b then 1 else y a b
  refine ⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], fun b P hP => ?_⟩
  haveI := P.isPrime
  have hPs : P ∈ hfin.toFinset := by simpa using hP
  obtain ⟨hlow, hdiag, hmod⟩ := Classical.choose_spec (hloc P hP)
  rw [← hξP P hP] at hlow hdiag hmod

  have hdiff : ∀ a, ξP P a b - ξ a b ∈ P.asIdeal ^ e P := by
    intro a
    by_cases hba : b < a
    · simp [ξ, hba, hlow a b hba]
    · by_cases hab : a = b
      · subst hab; simp [ξ, hdiag]
      · have := hy a b P hPs
        simp only [ξ, hba, hab, if_false]
        rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 this
  set L := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) with hL
  have key : ∀ (x : 𝓞 E) (v : S.V), ((x : E)) • v = x • v := fun x v => algebraMap_smul E x v
  have hterm : ∀ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a ∈ L := by
    intro a
    obtain ⟨s, hsP, hs⟩ := he P _ (hdiff a)
    obtain ⟨t, ht, htf⟩ := hf P hP a
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hsP ht, ?_⟩
    have : (s * t) • (((ξP P a b - ξ a b : 𝓞 E) : E) • f a) =
        (s * (ξP P a b - ξ a b)) • (t • f a) := by
      rw [key, smul_smul, smul_smul]
      congr 1; ring
    rw [this]
    exact Submodule.smul_mem_smul hs htf
  have hsplit : f' b - frameAct f ξ b =
      (f' b - frameAct f (ξP P) b) + ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a := by
    have hs : ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a =
        frameAct f (ξP P) b - frameAct f ξ b := by
      simp only [frameAct, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast; rw [sub_smul]
    rw [hs]; abel
  rw [hsplit]
  exact L.add_mem (hmod b) (L.sum_mem fun a _ => hterm a)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GxDoubleCoset
section
open scoped Classical ComplexConjugate ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

noncomputable section

namespace GlobalTheory.GxConj

variable {r n : ℕ}

theorem hJ_adj (ε : Fin n → Bool) (A Ai : Matrix (Fin n) (Fin n) ℂ)
    (hU : Aiᴴ * Formalism.REAL.Jm ε * Ai = Formalism.REAL.Jm ε) (h1 : Ai * A = 1) (x y : Fin n → ℂ) :
    hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y := by
  have e : Aiᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
    calc Aiᴴ * Formalism.REAL.Jm ε = Aiᴴ * Formalism.REAL.Jm ε * (Ai * A) := by rw [h1, Matrix.mul_one]
      _ = (Aiᴴ * Formalism.REAL.Jm ε * Ai) * A := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * A := by rw [hU]
  have e2 : Aiᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y) = Formalism.REAL.Jm ε *ᵥ (A *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, e2]

theorem hJ_sum_left {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ c, s c • x c) y = ∑ c, conj (s c) * hJ ε (x c) y := by
  unfold hJ
  simp only [star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_sum_right {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, s c • y c) = ∑ c, s c * hJ ε x (y c) := by
  unfold hJ
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem mulVec_lin {ι : Type*} [Fintype ι] (B : Matrix (Fin n) (Fin n) ℂ) (s : ι → ℂ) (y : ι → Fin n → ℂ) :
    B *ᵥ ∑ c, s c • y c = ∑ c, s c • (B *ᵥ y c) := by
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem zhat_conj (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (A Ai B C : Matrix (Fin n) (Fin n) ℂ)
    (hadj : ∀ x y, hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y) (L M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hL : ∀ a, Ai *ᵥ f a = ∑ c, L a c • f c) (hM : ∀ b, C *ᵥ f' b = ∑ d, M b d • f' d) :
    Zhat ε f f' (A * B * C) = L.map (starRingEnd ℂ) * Zhat ε f f' B * Mᵀ := by
  ext a b
  have e1 : (A * B * C) *ᵥ f' b = A *ᵥ (B *ᵥ (C *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp only [Formalism.L2.SG.RealObj.Zhat, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [e1, hadj, hL, hM, mulVec_lin, hJ_sum_left]
  simp only [hJ_sum_right, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.GxConj

namespace GlobalTheory

open GlobalTheory.GxConj

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticesLevelOneGenus
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tlat_one_genus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∃ h : UPts cm.sig J (Ad F), ∀ x, (h⁻¹).1.1 *ᵥ x ∈ hat F L ↔ x ∈ hat F M := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L M hT hS hf hL hM
  classical
  have hLat : IsLat L := hL.1
  have hMat : IsLat M := hM.1

  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ UPts cm.sig J (v.adicCompletion F),
      ∀ x, x ∈ loc v L ↔ g.1 *ᵥ x ∈ loc v M := by
    intro v
    by_cases hv : (T : 𝓞 F) ∈ v.asIdeal
    · exact _root_.GlobalTheory.St.G.exists_unitary_of_TLat F E cm n J hJ hdet T f L M hT hS hf hL hM v hv
    · exact _root_.GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt F E cm n J hJ hdet L M hLat hMat v
        (_root_.GlobalTheory.St.G.selfDualAt_of_tLat F E cm n J hJ hdet T f L hL v hv)
        (_root_.GlobalTheory.St.G.selfDualAt_of_tLat F E cm n J hJ hdet T f M hM v hv)
  choose g hgU hg using hloc

  let k : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
    fun v => if loc v L = loc v M then 1 else g v
  have hkU : ∀ v, k v ∈ UPts cm.sig J (v.adicCompletion F) := by
    intro v
    by_cases hv : loc v L = loc v M
    · simp only [k, if_pos hv]; exact one_mem _
    · simp only [k, if_neg hv]; exact hgU v
  have hfin : {v | k v ≠ 1}.Finite := by
    refine (_root_.GlobalTheory.St.G.loc_eq_almost_all F E n L M hLat hMat).subset ?_
    intro v hv heq
    exact hv (by simp only [k, if_pos heq])
  obtain ⟨y, hyU, hy⟩ := GlobalTheory.T.exists_adelic_unitary_of_finite_support F E n cm.sig J k hkU hfin
  have hglob : ∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M := by
    rw [GlobalTheory.T.adelicLattice_carry_iff_forall_place F E n L M hLat hMat y]
    intro v x
    rw [hy v]
    by_cases hv : loc v L = loc v M
    · simp only [k, if_pos hv, Units.val_one, Matrix.one_mulVec, hv]
    · simp only [k, if_neg hv]; exact hg v x
  refine ⟨⟨y, hyU⟩, fun x => ?_⟩
  rw [hglob, Matrix.mulVec_mulVec]
  have hinv : ((⟨y, hyU⟩ : UPts cm.sig J (Ad F))⁻¹).1 = y⁻¹ := rfl
  rw [hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
open Formalism.UG.P

namespace GlobalTheory.St.G.IntAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levelafC_natCast (m : ℕ) : levelafC (F := F) E (m : 𝓞 F) = (m : E ⊗[F] Ad F) := by
  induction m with
  | zero => simp only [levelafC, Nat.cast_zero, map_zero, TensorProduct.tmul_zero]
  | succ k ih =>
    simp only [levelafC] at ih ⊢
    rw [Nat.cast_succ, Nat.cast_succ, map_add (f := _), map_one, TensorProduct.tmul_add, ih,
      Algebra.TensorProduct.one_def]

private theorem sum_afsplitI_one_apply_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∈ S) : (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w = 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w =
      ∑ v ∈ S, (afsplitI v (1 : v.adicCompletion F)) w from map_sum (evalV F w) _ S]
  rw [Finset.sum_eq_single_of_mem w hw (fun v _ hv => afsplitI_ne v w (Ne.symm hv) 1),
    afsplitI_self]

private theorem sum_afsplitI_one_apply_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ S) : (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w =
      ∑ v ∈ S, (afsplitI v (1 : v.adicCompletion F)) w from map_sum (evalV F w) _ S]
  exact Finset.sum_eq_zero (fun v hv => afsplitI_ne v w (fun h => hw (by rw [h]; exact hv)) 1)

theorem mem_of_local (a : E ⊗[F] Ad F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) : a ∈ OAd F E := by
  classical
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) a
  have hfin := levelaf_finite_places (F := F) d hd0
  set S := hfin.toFinset with hS
  set dF : F := algebraMap (𝓞 F) F d with hdF
  have hdF0 : dF ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  set s : Ad F := ∑ v ∈ S, afsplitI v (1 : v.adicCompletion F) with hs
  set u : Ad F := (1 - s) * algebraMap F (Ad F) dF⁻¹ with hu
  have hu_int : u ∈ intAd F := by
    show ∀ w : HeightOneSpectrum (𝓞 F), u w ∈ w.adicCompletionIntegers F
    intro w
    have hcomp : u w = (1 - s w) * (dF⁻¹ • (1 : w.adicCompletion F)) := by
      rw [hu, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply,
        Algebra.algebraMap_eq_smul_one, afsplit_smul_apply, afsplit_one_apply]
    by_cases hw : w ∈ S
    · rw [hcomp, hs, sum_afsplitI_one_apply_of_mem S w hw, sub_self, zero_mul]
      exact zero_mem _
    · rw [hcomp, hs, sum_afsplitI_one_apply_of_not_mem S w hw, sub_zero, one_mul, Algebra.smul_def, mul_one, map_inv₀,
        HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      have h1 := levelaf_int_mem_v w d
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      have h2 : ¬ Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) d) < 1 :=
        fun hlt => hw (hfin.mem_toFinset.mpr hlt)
      have h3 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) d) = 1 :=
        le_antisymm h1 (not_lt.mp h2)
      rw [hdF, ← IsScalarTower.algebraMap_apply, h3, inv_one]
  have he : ∑ v ∈ S, afsplitEps E v = (1 : E) ⊗ₜ[F] s := by
    rw [hs, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h1 : (1 : E ⊗[F] Ad F) - ∑ v ∈ S, afsplitEps E v = ((1 : E) ⊗ₜ[F] u) * levelafC E d := by
    rw [he, levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hu, mul_assoc,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Ad F) d, ← hdF, ← map_mul, inv_mul_cancel₀ hdF0,
      map_one, mul_one, TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]
  have hsplit : a = (∑ v ∈ S, afsplitEps E v) * a + ((1 : E) ⊗ₜ[F] u) * (levelafC E d * a) := by
    rw [← mul_assoc, ← h1]
    ring
  rw [hsplit]
  refine add_mem ?_ (mul_mem ?_ hd)
  · rw [Finset.sum_mul]
    refine sum_mem (fun v _ => ?_)
    rw [← afsplit_decomp]
    exact afsplit_IE_int v _ (h v)
  · have hmem := levelaf_tmul_mem (E := E) (1 : 𝓞 E) hu_int
    rwa [map_one] at hmem

theorem expand_trace {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E)
    (a : E ⊗[F] Ad F) :
    a = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E (inclE (F := F) (Ad F) (β i) * a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero]
  | tmul e y =>
    have hT : ∀ i, adelstabT F E (inclE (F := F) (Ad F) (β i) * (e ⊗ₜ[F] y)) =
        Algebra.trace F E (e * β i) • y := by
      intro i
      rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, adelstabT_tmul, Algebra.smul_def, mul_comm (β i) e]
    simp_rw [hT, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    conv_lhs => rw [← ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β).sum_repr e]
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_add, map_add (f := _), TensorProduct.tmul_add]

private theorem adelstabT_inclE_of_forall_divisible (a : E ⊗[F] Ad F)
    (h : ∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) (e : E) :
    adelstabT F E (inclE (F := F) (Ad F) e * a) = 0 := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) (inclE (F := F) (Ad F) e)
  have hxS : inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) ∈ OAd F E := by
    rw [map_mul, adelstab_incl_C]
    exact hd
  have hzero : adelstabT F E (inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * a) = 0 := by
    refine GlobalTheory.IntegralFinAdele.eq_zero_of_forall_mul F _ (fun M hM => ?_)
    obtain ⟨t, ht, hat⟩ := h M hM
    refine ⟨adelstabT F E (inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * t),
      adelstabT_mem (mul_mem hxS ht), ?_⟩
    rw [hat, mul_left_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have hdF0 : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hxe : inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * a =
      algebraMap (𝓞 F) F d • (inclE (F := F) (Ad F) e * a) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E d, ← Algebra.smul_def, inclE,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      ← TensorProduct.smul_tmul', smul_mul_assoc]
  rw [hxe, map_smul] at hzero
  calc adelstabT F E (inclE (F := F) (Ad F) e * a)
      = (algebraMap (𝓞 F) F d)⁻¹ • algebraMap (𝓞 F) F d • adelstabT F E (inclE (F := F) (Ad F) e * a) :=
        (inv_smul_smul₀ hdF0 _).symm
    _ = 0 := by rw [hzero, smul_zero]

theorem eq_zero_of_multiples (a : E ⊗[F] Ad F)
    (h : ∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) : a = 0 := by
  classical
  rw [expand_trace (Module.Free.chooseBasis F E) a]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [adelstabT_inclE_of_forall_divisible a h, TensorProduct.tmul_zero]

theorem exists_nat_denom (a : E ⊗[F] Ad F) :
    ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) a
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  · rw [← levelafC_natCast, hq, levelafC_mul, mul_comm (levelafC E d), mul_assoc]
    exact mul_mem (levelafC_mem q) hd

theorem integral_adeles_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ a : E ⊗[F] Ad F, a ∈ OAd F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) ∧ (∀ a ∈ OAd F E, ∀ m : ℕ, 0 < m → ∃ x : 𝓞 E, ∃ t ∈ OAd F E, a = inclE (F := F) (Ad F) (x : E) + (m : E ⊗[F] Ad F) * t) ∧ (∀ a : E ⊗[F] Ad F, (∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) → a = 0) ∧ (∀ a : E ⊗[F] Ad F, ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E) ∧ (∀ x : E, inclE (F := F) (Ad F) x ∈ OAd F E ↔ x ∈ intOE E) := by
  intro F E _ _ _ _ _
  refine ⟨fun a => ⟨fun ha v => afsplit_prV_int v a ha, mem_of_local a⟩, ?_,
    fun a => eq_zero_of_multiples a, exists_nat_denom, fun x => ⟨?_, ?_⟩⟩
  · intro a ha m hm
    have hm' : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    obtain ⟨b, t, ht, hab⟩ := csGlob_approx (E := E) csGlob_intAdApprox (m : 𝓞 F) hm' a ha
    refine ⟨b, t, ht, ?_⟩
    rw [hab, levelafC_natCast]
    try rfl
  · intro hx
    exact ⟨⟨x, csGlob_int x hx⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact adelstab_incl_int b

end GlobalTheory.St.G.IntAd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConj
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem isClosed_range_of_isCompact_preimage {G H : Type} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (φ : G →* H) (hφ : Continuous φ) (U : Set H)
    (hU : IsOpen U) (h1 : (1 : H) ∈ U) (hc : IsCompact (φ ⁻¹' U)) : IsClosed (Set.range φ) := by
  have hcl : IsClosed (U ∩ Set.range φ) := by
    have e : U ∩ Set.range φ = φ '' (φ ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨hy, g, rfl⟩
        exact ⟨g, hy, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨hg, g, rfl⟩
    rw [e]
    exact (hc.image hφ).isClosed
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  have hO : IsOpen ((fun s => s⁻¹ * x) ⁻¹' U) := hU.preimage (by fun_prop)
  have hxO : x ∈ (fun s => s⁻¹ * x) ⁻¹' U := by
    show x⁻¹ * x ∈ U
    rwa [inv_mul_cancel]
  obtain ⟨s, hsU, g, rfl⟩ := mem_closure_iff.mp hx _ hO hxO
  have hy : (φ g)⁻¹ * x ∈ closure (Set.range φ) :=
    map_mem_closure (f := fun s => (φ g)⁻¹ * s) (by fun_prop) hx
      (by rintro _ ⟨k, rfl⟩; exact ⟨g⁻¹ * k, by simp⟩)
  have hyU : (φ g)⁻¹ * x ∈ U ∩ Set.range φ := by
    rw [← hcl.closure_eq]
    exact hU.inter_closure ⟨hsU, hy⟩
  obtain ⟨-, k, hk⟩ := hyU
  exact ⟨g * k, by rw [map_mul, hk, mul_inv_cancel_left]⟩

theorem nhds_one_hasBasis_Kg (I : AutInst) : (nhds (1 : I.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) I.Kg := by
  refine ⟨fun t => ⟨fun ht => I.topf_basis t ht, ?_⟩⟩
  rintro ⟨N, hN, hsub⟩
  refine Filter.mem_of_superset ((I.topf_open N hN).mem_nhds ?_) hsub
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  · simpa using one_mem (Formalism.UG.stabGL (lamAf (F := I.F) I.L))
  · simp

theorem isClosedEmbedding_of_preimage_Kg (I I' : AutInst) (φ : I'.Gf →* I.Gf)
    (h : ∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ φ g ∈ I.Kg N) : Topology.IsClosedEmbedding φ := by
  have hpre : (fun N : ℕ => φ ⁻¹' I.Kg N) = I'.Kg := by
    funext N
    ext g
    exact (h N g).symm
  have hb : (nhds (1 : I'.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) fun N => φ ⁻¹' I.Kg N := by
    rw [hpre]
    exact nhds_one_hasBasis_Kg I'
  have hind : Topology.IsInducing φ :=
    IsTopologicalGroup.isInducing_iff_nhds_one.mpr
      (hb.eq_of_same_basis ((nhds_one_hasBasis_Kg I).comap φ))
  have hT' := GlobalTheory.CongTop.adelic_topology I'
  haveI : T2Space I'.Gf := hT'.1
  haveI : T2Space I.Gf := (GlobalTheory.CongTop.adelic_topology I).1
  obtain ⟨hopen1, ⟨K, hK⟩, -⟩ := hT'.2.2.2.2.2.2 1 le_rfl
  have hKcl : IsClosed (I'.Kg 1) := by
    rw [← hK]
    exact K.isClosed_of_isOpen (by rw [hK]; exact hopen1)
  have hcpt : IsCompact (φ ⁻¹' I.Kg 1) := by
    rw [show φ ⁻¹' I.Kg 1 = I'.Kg 1 from congrFun hpre 1]
    exact hT'.2.2.2.1.of_isClosed_subset hKcl fun x hx => hx.1
  have hU : IsOpen (I.Kg 1) := ((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 1 le_rfl).1
  have h1 : (1 : I.Gf) ∈ I.Kg 1 := mem_of_mem_nhds ((nhds_one_hasBasis_Kg I).mem_of_mem le_rfl)
  exact ⟨hind.isEmbedding, isClosed_range_of_isCompact_preimage φ hind.continuous (I.Kg 1) hU h1 hcpt⟩

theorem isClosedEmbedding_of_conj_Kg : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf),
    (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  intro I I' j xf hj
  let ψ : I'.Gf →* I.Gf := (MulAut.conj xf⁻¹).toMonoidHom.comp j
  have hψ : ∀ g, ψ g = xf⁻¹ * j g * xf := fun g => by simp [ψ, MulAut.conj_apply]
  have hc : Topology.IsClosedEmbedding ψ :=
    isClosedEmbedding_of_preimage_Kg I I' ψ fun N g => by rw [hψ]; exact hj N g
  have e : (j : I'.Gf → I.Gf) = ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)) ∘ ψ := by
    funext g
    simp [hψ, mul_assoc]
  rw [e]
  exact ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)).isClosedEmbedding.comp hc

end GlobalTheory.StabUnfold
end

