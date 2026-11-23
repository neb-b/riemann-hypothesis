module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSet
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevRedTriv

open Formalism.L2.DIV

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem coord_mem_idS {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (PP.asIdeal • Λ)) (i : Fin n) :
    ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z) i := by
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 with hB
  revert i
  refine Submodule.span_induction
    (p := fun z _ => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (B *ᵥ z) i)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on
      (p := fun x => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        (B *ᵥ fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) i) hx ?_ ?_
    · intro p hp l hl i
      have hlm : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨l, hl, rfl⟩
      have ht := (hβ _).1 hlm i
      refine ⟨oToS F E p * ⟨_, ht⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp), ?_⟩
      have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((p • l) i)) =
          ((oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) •
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
        funext k
        rw [Pi.smul_apply, Pi.smul_apply, oToS_coe, smul_eq_mul]
        show ((p : E) * l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) =
          (algebraMap (𝓞 E) E p) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) * ((l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
    · intro x₁ x₂ h₁ h₂ i
      obtain ⟨s₁, hs₁, e₁⟩ := h₁ i
      obtain ⟨s₂, hs₂, e₂⟩ := h₂ i
      refine ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, ?_⟩
      have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((x₁ + x₂) i)) =
          (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₁ i)) +
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₂ i)) := by
        funext k; simp
      rw [e, Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]
  · intro i
    exact ⟨0, Ideal.zero_mem _, by simp⟩
  · intro a c _ _ ha hc i
    obtain ⟨s₁, hs₁, e₁⟩ := ha i
    obtain ⟨s₂, hs₂, e₂⟩ := hc i
    exact ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, by rw [Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]⟩
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    have : c • a = ((c : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • a := rfl
    rw [this, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]

theorem coe_sub_one_apply (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (i j : Fin n) :
    (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = ((intGL F E n y).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem conj_sub_one {R : Type} [CommRing R] {m : ℕ} (β : GL (Fin m) R) (X Y : Matrix (Fin m) (Fin m) R)
    (h : X = β.1 * Y * (β⁻¹).1) : Y - 1 = (β⁻¹).1 * (X - 1) * β.1 := by
  subst h
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem map_smul_sub {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (f : A →+* B) (c : A) (c' : B) (hc : f c = c')
    (M : Matrix (Fin m) (Fin m) A) (u : Fin m → A) (w : Fin m → B) (hu : ⇑f ∘ u = w) :
    (fun i => f ((c • (M *ᵥ u - u)) i)) = c' • ((M.map f - 1) *ᵥ w) := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hc, Pi.sub_apply, map_sub,
    RingHom.map_mulVec, hu, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hu]
  rfl

theorem col_entry {R : Type} [CommRing R] {m : ℕ} (β : GL (Fin m) R) (X Y : Matrix (Fin m) (Fin m) R)
    (e2 : Y - 1 = (β⁻¹).1 * (X - 1) * β.1) (c : R) (i j : Fin m) :
    ((β⁻¹).1 *ᵥ (c • ((X - 1) *ᵥ (β.1 *ᵥ Pi.single j 1)))) i = c * (Y - 1) i j := by
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← e2,
    Matrix.mulVec_single_one]
  rfl

theorem redFn_eq_one_of_cols {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ St β) (b : 𝓞 E)
    (hb : b ∉ PP.asIdeal)
    (h : ∀ j, ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) •
      ((x.1 - 1) *ᵥ (β.1 *ᵥ Pi.single j 1)) ∈ Formalism.L2.Herm.hatL (F := F) (PP.asIdeal • Λ)) :
    redFn β PP x = 1 := by
  obtain ⟨y, rfl⟩ := hx
  have e2 : (intGL F E n y).1 - 1 = (β⁻¹).1 * ((frGL β y).1 - 1) * β.1 := conj_sub_one β _ _ rfl
  have hprime : PP.asIdeal.IsPrime := PP.isPrime
  have hb0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
  rw [redFn_frGL]
  apply Units.ext
  ext i j
  obtain ⟨s, hs, es⟩ := coord_mem_idS hβ PP (h j) i
  rw [col_entry β _ _ e2] at es
  have es' : s = oToS F E b * (y.1 - 1) i j := by
    apply Subtype.ext
    rw [Subring.coe_mul, coe_sub_one_apply, es]
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    have h0 : resS F PP s = 0 := by
      rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff]; exact hs
    rw [es', map_mul, resS_oToS] at h0
    exact (mul_eq_zero.1 h0).resolve_left hb0
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end General

section Adelic


set_option maxHeartbeats 1000000 in
theorem col_cong (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β L) (k : GA D V) (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E)
    (h : ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L))
    (w : Fin V.rank → Lev.EAf D) (hw : w ∈ Formalism.L2.Herm.hatL (F := D.host.F) L) :
    ((oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) •
      (((Lev.finE V k).1 - 1) *ᵥ w) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (PP.asIdeal • L) := by
  have eX : (Lev.finE V k).1 = (fmt V k).map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := rfl
  rw [eX]
  choose u hu using fun i => (GlobalTheory.LevSplit.swp_bij (F := D.host.F) (E := D.host.E)).2 (w i)
  have hu' : (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (u i)) = w := funext hu
  have hc : ⇑(GlobalTheory.LevSplit.swp D.host.F D.host.E) ∘ u = w := funext hu
  have hum : u ∈ hatV L := (GlobalTheory.LevSplit.latHat_iff L u).2 (by rw [hu']; exact hw)
  have h1 := (GlobalTheory.LevSplit.latHat_iff (PP.asIdeal • L) _).1 (h u hum)
  have eb : GlobalTheory.LevSplit.swp D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) =
      ((oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := by
    rw [GlobalTheory.LevSplit.swp_tmul, oToS_coe]
  rw [map_smul_sub (GlobalTheory.LevSplit.swp D.host.F D.host.E) _ _ eb (fmt V k) u w hc] at h1
  exact h1

theorem redFn_eq_one_of_cong (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β L) (k : GA D V) (hk : Lev.finE V k ∈ Formalism.L2.DIV.St β)
    (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E) (hb : b ∉ PP.asIdeal)
    (h : ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L)) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 :=
  redFn_eq_one_of_cols hβ PP _ hk b hb fun j =>
    col_cong D V L β hβ k PP b h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hβ j)

end Adelic

end GlobalTheory.LevRedTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityVanishingAndSameParamsSubspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this


open GlobalTheory.LFun.ParLin in
theorem isPar_add_smul : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' →
    (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) →
    u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  intro D c s
  have cne : ∀ f : GA D s.V → ℂ, f ≠ 0 → (fun g => conj (f g)) ≠ 0 := fun f hf h0 =>
    hf (funext fun g => by simpa using congrFun h0 g)
  refine ⟨fun u u' B B' a hu hu' hB h0 => ⟨h0, fun v hv => ?_⟩, fun u B a hu ha => ⟨smul_ne_zero ha hu.1, fun v hv => ?_⟩⟩
  · have hval : PiLocalization₂.val (u + a • u') v = PiLocalization₂.val u v + a • PiLocalization₂.val u' v := by simp [PiLocalization₂.val]
    have hc : (fun g => conj (PiLocalization₂.val (u + a • u') v g)) =
        (fun g => conj (PiLocalization₂.val u v g)) + (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    by_cases h1 : PiLocalization₂.val u v = 0
    · have h2 : a • PiLocalization₂.val u' v ≠ 0 := by rw [hval, h1, zero_add] at hv; exact hv
      have ha : a ≠ 0 := fun e => h2 (by simp [e])
      have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
      have hz : (fun g => conj (PiLocalization₂.val u v g)) = 0 := by funext g; simp [h1]
      rw [hz, zero_add]
      exact paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)
    · by_cases h2 : a • PiLocalization₂.val u' v = 0
      · have hz : (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) = 0 := by
          funext g
          have := congrFun h2 g
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          rw [← map_mul, this, map_zero]
        rw [hz, add_zero]
        exact hu.2 v h1
      · have ha : a ≠ 0 := fun e => h2 (by simp [e])
        have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
        refine paramFun_add (hu.2 v h1) (paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)) ?_
        rw [← hc]
        exact cne _ hv
  · have hval : PiLocalization₂.val (a • u) v = a • PiLocalization₂.val u v := by simp [PiLocalization₂.val]
    have hu0 : PiLocalization₂.val u v ≠ 0 := fun e => hv (by rw [hval, e, smul_zero])
    have hc : (fun g => conj (PiLocalization₂.val (a • u) v g)) = (conj a) • (fun g => conj (PiLocalization₂.val u v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    exact paramFun_smul (hu.2 v hu0) (by simpa using ha)

theorem vanish_and_parLin : ∀ D : D7, MetEx D → (ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0) ∧ ∀ (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B :=
  fun D hM => ⟨val_eq_zero_imp D hM, isPar_add_smul D⟩

end GlobalTheory.EvenOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyAlgHomCompletionOfSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitPlaceEmb

theorem not_isField_of_idem {A : Type} [CommRing A] (σ : A →+* A) {z : A} (hz : z * z = z) (h : z + σ z = 1) :
    ¬ IsField A := by
  intro hf
  haveI := hf.isDomain
  have h0 : z * (z - 1) = 0 := by rw [mul_sub, hz, mul_one, sub_self]
  rcases mul_eq_zero.1 h0 with h' | h'
  · rw [h', σ.map_zero, zero_add] at h
    exact zero_ne_one h
  · rw [sub_eq_zero.1 h', σ.map_one] at h
    exact one_ne_zero (add_eq_left.1 h)

theorem nonempty_algHom_of_idem {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    (hE : Module.finrank F E = 2) (σ : E →ₐ[F] E) {z : K ⊗[F] E} (hz : z * z = z)
    (h : z + (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom z = 1) : Nonempty (E →ₐ[F] K) := by
  have h2 : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, hE]
  obtain ⟨φ⟩ := GlobalTheory.AdelicU.nonempty_algHom_of_not_isField (K := K) h2
    (not_isField_of_idem (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom hz h)
  exact ⟨(φ.restrictScalars F).comp Algebra.TensorProduct.includeRight⟩

theorem nonempty_algHom_of_idem_map {F E K R : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    [CommRing R] [Algebra F R] (hE : Module.finrank F E = 2) (σ : E →ₐ[F] E) (ψ : R →ₐ[F] K) {e : R ⊗[F] E}
    {ε : R} (he : e * e = e) (hs : e + (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom e = algebraMap R _ ε)
    (hψ : ψ ε = 1) : Nonempty (E →ₐ[F] K) := by
  let Φ : R ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map ψ (AlgHom.id F E)).toRingHom
  let τ : K ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom
  have hcomm : ∀ x, Φ ((Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom x) = τ (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine nonempty_algHom_of_idem hE σ (z := Φ e) (by rw [← map_mul, he]) ?_
  have := congrArg Φ hs
  rw [map_add (f := _), hcomm] at this
  rw [this, Algebra.TensorProduct.algebraMap_apply]
  change ψ ε ⊗ₜ[F] (1 : E) = 1
  rw [hψ]
  rfl

theorem nonempty_algHom_of_not_nonSplitAt :
    ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ¬ GlobalTheory.WeilParts.NonSplitAt D v ε → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := by
  intro D v ε hε hn
  obtain ⟨e, ⟨he, -, -⟩, hsum⟩ : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap _ _ ε := by
    by_contra h
    exact hn ⟨hε, h⟩
  obtain ⟨α, rfl, h1, -⟩ := hε
  exact nonempty_algHom_of_idem_map (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 D.sp.cm.sig
    ((evalV D.host.F v).comp (sndA D.host.F)) he hsum h1

end GlobalTheory.SplitPlaceEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumWordCombinationCoefficientsLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.IoPhase

open GlobalTheory.ConjLiftUnique

theorem isONBasis_of_adapted {n : ℕ} {G B : Mn n} (h : IsAdapted G 1 B) : IsONBasis G 1 B n := by
  obtain ⟨ε, h1, h2⟩ := h
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have c : Formalism.REAL.Jm ε * (Bᴴ * G) * B = 1 := by rw [Matrix.mul_assoc, h1, hJ]
  have e : Formalism.REAL.Jm ε = 1 := by
    calc Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Bᴴ * G) * B * Formalism.REAL.Jm ε := by rw [c, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc _ B, ← h2, Matrix.one_mul, c]
  exact ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [h1, e], by simp⟩

theorem io_eq_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}
    (hω : IsWeilDatumO ψ V W χV χW ω) (h1 : Formalism.IndefR.FWT.LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    (hc : c.Is) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)) (ht : ∀ P, IsThetaFunO ψ V W (pt P))
    (hinj : Function.Injective pt) {Δ : PolF D W.rank V.rank}
    {io io' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    (hio' : IsIoW θ M c ω pt Δ io') : ∃ a : ℂ, ‖a‖ = 1 ∧ io' = a • io := by
  classical
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W := io.compr₂ (pt.codRestrict (thetaSub ψ V W) ht)
  let F' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W := io'.compr₂ (pt.codRestrict (thetaSub ψ V W) ht)
  have f1 : ∀ x w, (F x w).1 = pt (io x w) := fun _ _ => rfl
  have f2 : ∀ x w, (F' x w).1 = pt (io' x w) := fun _ _ => rfl
  clear_value F F'
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  have hF' : Eqv θ ω F' := ⟨fun u hu x w => by rw [f2, f2, hio'.1 u hu],
    fun τ k hk v u hu w => by rw [f2, f2, hio'.2.1 τ k hk v u hu]⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₁, w₁, n1', n2', e'⟩ := hio'.2.2
  obtain ⟨b, hb⟩ := exists_invForm hω
  obtain ⟨c₁, k1⟩ := exists_const_of_eqv h1 h2 hc hb hF hF w₀ n2
  obtain ⟨c₂, k2⟩ := exists_const_of_eqv h1 h2 hc hb hF' hF' w₀ n2
  obtain ⟨c₃, k3⟩ := exists_const_of_eqv h1 h2 hc hb hF hF' w₀ n2
  obtain ⟨κ, hκ, hk⟩ := exists_phase b hb.symm hb.pos hb.defin (fun v w => F (PiTensorProduct.tprod ℂ v) w)
    (fun v w => F' (PiTensorProduct.tprod ℂ v) w) k1 k2 k3 n1 n1' n2 n2' (l := 1) norm_one
    (Subtype.ext (by rw [one_smul, f1, f2, e, e']))
  have hFF : F' = κ • F := PiTensorProduct.ext (MultilinearMap.ext fun v => LinearMap.ext (hk v))
  refine ⟨κ, hκ, LinearMap.ext fun x => LinearMap.ext fun w => hinj ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← f1, ← f2, hFF]
  rfl

theorem ioUniq (D : D7) : IoUniq D := by
  intro i M M' ψ θ χS χT ω hθ hω _ c hc _ BV f hf io io' hio hio'
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h : ∃ ρ, tauE D ρ = σ
    · exact ⟨h.choose⟩
    · exact ⟨(not_not.1 fun h' => h ((GlobalTheory.PointAtPlace.tauE_cm σ).2 h')).choose⟩
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ M' fun τ =>
    GlobalTheory.LowSmooth.shape_at M' τ (D.hc τ) (Formalism.IndefR.FWT.rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ) rfl
  have hB := fun τ => isONBasis_of_adapted (hf τ).onS
  exact io_eq_smul hω hlow.1 hlow.2 hc _
    (GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M') (onb M') (hf τ₀).theta)
    (GlobalTheory.FockIndep.pureTensorO_injective D ψ θ _ _ _ M' BV f hω.std hθ
      (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hB τ)) hB (hf τ₀).theta (hf τ₀).ne fun τ => (hf τ).vac) hio hio'

theorem ioUniq_of_discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoUniq D :=
  fun _ _ => ioUniq

end GlobalTheory.ArchRec.IoPhase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedNormSqFourierEqIsotropicMatrixCoeff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResNormFourier

theorem resNorm_fourier : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f, IsThetaFunO ψ V W f → ∀ y : Mx D W.rank r, ∫ w in 𝓕₀, heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f w * starRingEnd ℂ (f w) ∂μ₀ = ∫ u, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) * GlobalTheory.LeviNorm.resNorm ψ V V' W C C' B μ 𝓨 μ' 𝓕' f u ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hY μ₀ 𝓕₀ h0 μ' 𝓕' h' f hf y
  have L := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have hR := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hY
  obtain ⟨-, -, hP⟩ := _root_.GlobalTheory.MixParseval.parseval D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hY μ₀ 𝓕₀ h0 μ' 𝓕' h' _ f
    (L.1 _ f hf) hf
  rw [hP]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hsm : ∀ (c : ℂ) (g : WO V W → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (c • g) =
      c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 g := by
    intro c g; funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  have key : ∀ a b : WO V W, heisO ψ V W a (heisO ψ V W b f) =
      ψ (symplOH V W a b + symplOH V W a b) • heisO ψ V W b (heisO ψ V W a f) := by
    intro a b
    rw [L.2.1 a b f, L.2.1 b a f, smul_smul, add_comm b a, GlobalTheory.MixModel.symplOH_skew V W b a,
      ← AddChar.map_add_eq_mul]
    congr 2
    abel
  simp only
  rw [key, hsm, (hR.1 _ (L.1 _ f hf)).2.2.2 y]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  rfl

end GlobalTheory.ResNormFourier
end

