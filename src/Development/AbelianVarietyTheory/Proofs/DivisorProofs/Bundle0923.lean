module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0888
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusCharacterUnitActionProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MovedLat

open GlobalTheory.AdelicLatMove GlobalTheory.AdLat Formalism.IndefR

variable {D : D7}

theorem hat_hLat (V : HSp D) (g : Bridge.Gf V) :
    (hat D.host.F (Bridge.hLat V g : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA D.host.F D.host.E)) =
      g.1.1.mulVec '' (hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, -, -, h⟩ := exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) g.1 hfg hsp
  rw [GlobalTheory.RepsCompare.coe_hLat, ← hΛ, h]

theorem hLat_one (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  apply SetLike.coe_injective
  rw [GlobalTheory.RepsCompare.coe_hLat]
  ext x
  rw [SetLike.mem_coe, ← (hat_rational_points_and_approx D.host.F D.host.E _ _ hfg hsp).1]
  simp [GlobalTheory.AdLat.latOf]

theorem isSelfDualC_hLat (V : HSp D) (g : Bridge.Gf V) : IsSelfDualC V (Bridge.hLat V g) := by
  refine ⟨GlobalTheory.RepsCompare.isLattice_hLat V g, fun v => ?_⟩
  obtain ⟨-, -, hfg, hsp, c2, -, -, gh, gd, -, hsd⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := latOf_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D) V.gramᵀ 1 g.1 hfg hsp c2 gh gd
    one_ne_zero hsd (GlobalTheory.RepsCompare.isUnA_gf V g)
  rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, ← key, ← GlobalTheory.RepsCompare.coe_hLat]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : ∑ i, ∑ j, star (y i) * V.gram i j * v j = ∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change star (y b) * V.gram b a * v a = v a * V.gram b a * star (y b)
    ring
  rw [e, FractionalIdeal.mem_one_iff]

theorem mulVec_mem_hatL (V : HSp D) (g : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (H : ∀ z ∈ hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (finHom V g).1 *ᵥ z ∈ hat D.host.F (Λ' : Set (Fin V.rank → D.host.E)))
    (x : Fin V.rank → EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  have h := GlobalTheory.PrincInLevel.swap_mem_hatL Λ' _ (H _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ x hx))
  convert h using 1
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul, toEAf, finPart,
    finHom, Formalism.L2.Theta.mt, Formalism.UG.bc]

theorem actO_mem (S T : HSp D) (g : GA D S) (h : GA D T)
    (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ z ∈ hat D.host.F (ΛS : Set (Fin S.rank → D.host.E)),
      (finHom S g).1 *ᵥ z ∈ hat D.host.F (ΛS' : Set (Fin S.rank → D.host.E)))
    (hT : ∀ z ∈ hat D.host.F (ΛT : Set (Fin T.rank → D.host.E)),
      (finHom T h).1 *ᵥ z ∈ hat D.host.F (ΛT' : Set (Fin T.rank → D.host.E)))
    (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈
      latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, actO_rankOne]
    exact rankOne_mem_latO S T ΛS' ΛT' a ha _
      (mulVec_mem_hatL S g ΛS ΛS' hS _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_hatL T h ΛT ΛT' hT _ (pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem fwd (V : HSp D) (g : GA D V) : ∀ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
    (finHom V g).1 *ᵥ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [← SetLike.mem_coe, hat_hLat]
  exact ⟨z, hz, rfl⟩

theorem bwd (V : HSp D) (g : GA D V) :
    ∀ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)),
    (finHom V g⁻¹).1 *ᵥ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [← SetLike.mem_coe, hat_hLat] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  change (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) ∈ _
  rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  exact hy

theorem latG_eq (W : HSp D) (k : GA D W) : Formalism.L2.Pj.latG W k = Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat W (FWT.fin W k), w = a • v} := by
  have key : ∀ v, Formalism.L2.Pj.finVec W v ∈ Formalism.L2.Pj.gLat W k ↔ v ∈ Bridge.hLat W (FWT.fin W k) := by
    intro v
    rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, Formalism.L2.Pj.gLat, (GlobalTheory.Member.latHat_eq_hat_and_gram D W).1]
    exact Iff.rfl
  unfold Formalism.L2.Pj.latG
  simp only [key]

theorem moved_lattices : ∀ (D : D7) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (h : GA D V) (k : GA D W), IsSelfDualC V (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧ IsSelfDualC W (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k)) ∧ (∀ u : WO V W, u ∈ (latO V W (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h) : Set (Fin V.rank → D.host.E)) (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u = actO V W h k u₀) ∧ Formalism.L2.Pj.latG W k = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k), w = a • v} ∧ Formalism.IndefR.Bridge.hLat V 1 = ΛV ∧ Formalism.IndefR.Bridge.hLat W 1 = ΛW := by
  intro D V W ΛV ΛW hV hW _ _ h k
  obtain rfl : ΛV = GlobalTheory.Member.latC V := SetLike.coe_injective (hV.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  obtain rfl : ΛW = GlobalTheory.Member.latC W := SetLike.coe_injective (hW.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq W).symm)
  refine ⟨isSelfDualC_hLat V _, isSelfDualC_hLat W _, fun u => ⟨fun hu => ?_, ?_⟩, latG_eq W k, hLat_one V, hLat_one W⟩
  · exact ⟨_, actO_mem V W h⁻¹ k⁻¹ _ _ _ _ (bwd V h) (bwd W k) u hu, (actO_actO_inv V W h k u).symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    exact actO_mem V W h k _ _ _ _ (fwd V h) (fwd W k) u₀ hu

end GlobalTheory.MovedLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

namespace GlobalTheory.DefTransfer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def KP [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) : Set (UA D.host.E n) :=
  {x | x ∈ locU n P ∧ cLoc P x ∈ GlobalTheory.LFun.KGL P (n := n)}

def cj [IsCMField D.host.E] {V : HSp D} (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V) :
    UA D.host.E V.rank ≃* GA D V :=
  j.toMulEquiv.trans (MulAut.conj h₀⁻¹)

theorem cj_apply [IsCMField D.host.E] {V : HSp D} (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (x : UA D.host.E V.rank) : cj j h₀ x = h₀⁻¹ * j x * h₀ := by
  simp [cj, MulAut.conj_apply]
  rfl

def IsTransfer [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V) : Prop :=
  h₀ ∈ GfC V ∧
  (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) ∧
  (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) ∧
  (∀ x, x ∈ infU D.host.E V.rank ↔ j x ∈ GinfC V) ∧
  (∃ A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (A τ)) ∧
    ∀ τ x, infMat D.sp.cm.sig V.gram (θ τ) (j x) =
      A τ * (cEmb (tauE D τ) x : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (A τ)⁻¹) ∧
  (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x,
    x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ ∃ e f, IsPrimeIdem P e f ∧ SuppF V f (cj j h₀ x)) ∧
  (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P) ∧
  ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) d R, GlobalTheory.Hk3.SphOp V P d R →
    (∀ γ ∈ R, (cj j h₀).symm γ ∈ locU V.rank P ∧ HasDiv (Ov D.host.E P) d (cLoc P ((cj j h₀).symm γ))) ∧
    ∀ x ∈ locU V.rank P, HasDiv (Ov D.host.E P) d (cLoc P x) →
      ∃! γ, γ ∈ R ∧ ((cj j h₀).symm γ)⁻¹ * x ∈ KP V.rank P

variable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

variable {θ M}

end GlobalTheory.DefTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPowe
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

noncomputable section

namespace GlobalTheory.IwasawaGL

theorem diagPow_val {K : Type} [Field K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    ((GlobalTheory.JSW.diagPow ϖ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => ((ϖ ^ l i : Kˣ) : K)) := rfl

theorem exists_unit_part (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (x : w.adicCompletion E)
    (hx : x ≠ 0) :
    ∃ e : ℤ, Valued.v (x * ((ϖ ^ (-e) : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = 1 := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.1 h0
  refine ⟨-Multiplicative.toAdd γ, ?_⟩
  rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← hγ, neg_neg,
    ← WithZero.coe_zpow, ← WithZero.coe_mul]
  rw [show (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

theorem iwasawa_diagPow : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w (n := a), g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  intro E _ _ a w ϖ hϖ g
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.spherical_iwasawa E w g
  have hd : ∀ i, (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i ≠ 0 :=
    Formalism.UG.P.spherical_diag_ne_zero b hb
  choose e he using fun i => exists_unit_part E w ϖ hϖ _ (hd i)
  let c : Fin a → w.adicCompletion E := fun i =>
    (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i * ((ϖ ^ (-e i) : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have hc0 : ∀ i, c i ≠ 0 := fun i => mul_ne_zero (hd i) (Units.ne_zero _)
  have hcO : ∀ i, c i ∈ Ov E w := fun i => (he i).le
  have hcO' : ∀ i, (c i)⁻¹ ∈ Ov E w := fun i => by
    show Valued.v (c i)⁻¹ ≤ 1
    rw [map_inv₀, he i, inv_one]
  let Dc : GL (Fin a) (w.adicCompletion E) :=
    ⟨Matrix.diagonal c, Matrix.diagonal (fun i => (c i)⁻¹),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hc0 i),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hc0 i)⟩
  have hDc : Dc ∈ KGL w (n := a) := by
    refine Formalism.UG.P.glint_mem_range_of_integral (Ov E w) Dc
      ⟨Matrix.diagonal (fun i => (⟨c i, hcO i⟩ : Ov E w)), ?_⟩
      ⟨Matrix.diagonal (fun i => (⟨(c i)⁻¹, hcO' i⟩ : Ov E w)), ?_⟩
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc]
      split_ifs <;> simp
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc, Units.inv_mk]
      split_ifs <;> simp
  let N : ℕ := ∑ i, (e i).natAbs
  let l : Fin a → ℕ := fun i => (e i + N).toNat
  have hexp : ∀ i, ((ϖ⁻¹) ^ N * ϖ ^ (l i) : (w.adicCompletion E)ˣ) = ϖ ^ (e i) := by
    intro i
    have hle : (e i).natAbs ≤ N :=
      Finset.single_le_sum (f := fun j => (e j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h1 : -((e i).natAbs : ℤ) ≤ e i := by rw [Int.natCast_natAbs]; exact neg_abs_le _
    have h2 : ((e i).natAbs : ℤ) ≤ N := by exact_mod_cast hle
    have hl : ((l i : ℕ) : ℤ) = e i + N := Int.toNat_of_nonneg (by omega)
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add, hl]
    congr 1; ring
  have hT : ((GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc : GL (Fin a) (w.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) := by
    rw [Units.val_mul, Units.val_mul, diagPow_val, diagPow_val]
    change Matrix.diagonal _ * Matrix.diagonal _ * Matrix.diagonal c = _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← Units.val_mul, hexp i]
    simp only [c]
    rw [mul_left_comm, ← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]
  let u : GL (Fin a) (w.adicCompletion E) := b * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc)⁻¹
  have hu : u * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc) = b := by
    simp only [u]; group
  have hmat : (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) = b := by
    rw [← hT, ← Units.val_mul, hu]
  have hent : ∀ i j, (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j *
      (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) j j = (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
    intro i j
    have := congrFun (congrFun hmat i) j
    rwa [Matrix.mul_diagonal] at this
  have hmem : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := hent i j
      rw [hb hij] at h
      exact (mul_eq_zero.1 h).resolve_right (hd j)
    · exact mul_right_cancel₀ (hd i) (by rw [one_mul]; exact hent i i)
  refine ⟨u, hmem, N, l, Dc * k, Subgroup.mul_mem _ hDc hk, ?_⟩
  simp only [u]
  group

end GlobalTheory.IwasawaGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStabIffIsKStableOnFiniteVectors
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.KFinStab

theorem kStab_iff_kStableOn : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ U : Submodule ℂ D, FiniteDimensional ℂ U → (KStab ε E U ↔ IsKStableOn ε σ (U.map D.subtype)) := by
  intro n ε H _ _ σ D E hc hσ hirr hK U hU
  obtain ⟨S, E', hS⟩ := CompanionTheory.D.DSIC.hSmMod n ε H σ hσ
  have hDS : D ≤ S := fun v hv =>
    (hS.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n ε H σ hσ hirr v ((hK.mem v).1 hv))
  set ι := Submodule.inclusion hDS with hι
  have hιinj : Function.Injective ι := Submodule.inclusion_injective hDS
  have hE : ∀ a b (v : D), E' a b (ι v) = ι (E a b v) := by
    intro a b v
    have key := GlobalTheory.realForm_spans n ε H (fun a b => (E a b v : H) - (E' a b (ι v) : H)) ?_ a b
    · apply Subtype.ext
      exact (sub_eq_zero.1 key).symm
    intro X hX
    have h1 := hK.real X hX v
    have h2 := hS.real X hX (ι v)
    have h3 : ((ι v : S) : H) = (v : H) := rfl
    rw [h3] at h2
    have h4 := h1.unique h2
    simp only [smul_sub, Finset.sum_sub_distrib, h4, sub_self]
  have hmap : (U.map ι).map S.subtype = U.map D.subtype := by
    rw [← Submodule.map_comp]
    rfl
  have : FiniteDimensional ℂ (U.map ι) := inferInstance
  have hL := CompanionTheory.D.DSIC.hStabLink n ε H σ S E' hσ hS (U.map ι) inferInstance
  rw [hmap] at hL
  refine Iff.trans ?_ hL
  constructor
  · intro h a b hab w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [hE]
    exact Submodule.mem_map_of_mem (h a b hab v hv)
  · intro h a b hab v hv
    have := h a b hab (ι v) (Submodule.mem_map_of_mem hv)
    rw [hE] at this
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 this
    rwa [← hιinj hxe]

end GlobalTheory.KFinStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjDataStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.PointSumConj.pointSum_conj_data) | (exact GlobalTheory.PointSumConj.pointSum_conj_data) | (intros; apply GlobalTheory.PointSumConj.pointSum_conj_data  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalenceStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPairScalarIsomorphic_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  first | (exact @GlobalTheory.LKMid.Pair.rel_equivalence) | (exact GlobalTheory.LKMid.Pair.rel_equivalence) | (intros; apply GlobalTheory.LKMid.Pair.rel_equivalence  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_cohomology_injective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → (∀ j : ℤ, Subsingleton (Ht q (sp A) 1 j)) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = 0 → x = 0 := by
  first | (exact @GlobalTheory.EtC.kerLaurent) | (exact GlobalTheory.EtC.kerLaurent) | (intros; apply GlobalTheory.EtC.kerLaurent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApproxStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox : EpsSt → LimActSt := by
  first | exact @GlobalTheory.IsoTriv.limActSt_of_epsSt | exact GlobalTheory.IsoTriv.limActSt_of_epsSt | (intros; apply GlobalTheory.IsoTriv.limActSt_of_epsSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankThreeLtTop
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin3

theorem norm_one_add_conj_mul (z : ℂ) : ‖1 + (starRingEnd ℂ) z * z‖ = 1 + ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', show (1 : ℂ) + (‖z‖ : ℂ) ^ 2 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_of_nonneg (by positivity)]

theorem gB_one (w : Low 3 → ℂ) : gB 1 w = (1 + ‖w ⟨(2, 1), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

theorem gB_two (w : Low 3 → ℂ) : gB 2 w = (1 + ‖w ⟨(1, 0), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

noncomputable def dom (x : ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) 1).indicator 1 x + ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2))

theorem measurable_dom : Measurable dom := by
  unfold dom
  refine Measurable.add ((measurable_const).indicator Metric.isClosed_closedBall.measurableSet) ?_
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

theorem lintegral_dom_lt_top : ∫⁻ x, dom x < ⊤ := by
  unfold dom
  rw [lintegral_add_left (f := (Metric.closedBall (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞))
    (measurable_one.indicator Metric.isClosed_closedBall.measurableSet)]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · rw [lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]
    exact measure_closedBall_lt_top
  · exact (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)).lintegral_lt_top

theorem le_prod_dom (w : Low 3 → ℂ) (e : Low 3) (hw : ∀ p, p ≠ e → ‖w p‖ ≤ 1) :
    ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) ≤ ∏ p, dom (w p) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  calc ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) = ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) * 1 :=
        (mul_one _).symm
    _ ≤ dom (w e) * ∏ p ∈ Finset.univ.erase e, dom (w p) := by
      refine mul_le_mul' ?_ ?_
      · unfold dom
        refine le_trans (le_of_eq ?_) le_add_self
        congr 1
        rw [show (-(4 : ℝ) / 2) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      · refine Finset.one_le_prod' fun p hp => ?_
        unfold dom
        refine le_trans (le_of_eq ?_) le_self_add
        rw [Set.indicator_of_mem (by simpa using hw p (Finset.ne_of_mem_erase hp))]
        rfl

theorem hB_le (p0 : ℕ) (hp : p0 = 1 ∨ p0 = 2) (w : Low 3 → ℂ) : hB p0 w ≤ ∏ p, dom (w p) := by
  unfold hB
  by_cases hS : w ∈ {w : Low 3 → ℂ | ∀ p : Low 3, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
  · rw [Set.indicator_of_mem hS]
    rcases hp with rfl | rfl
    · rw [gB_one]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
    · rw [gB_two]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
  · rw [Set.indicator_of_notMem hS]
    exact bot_le

theorem lintegral_hB_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  intro p0 hp
  refine lt_of_le_of_lt (lintegral_mono fun w => hB_le p0 hp w) ?_
  have h := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (E := fun _ : Low 3 => ℂ)
    (μ := fun _ => (volume : Measure ℂ)) (f := fun _ => dom) (fun _ => measurable_dom.aemeasurable)
  rw [volume_pi, h]
  exact ENNReal.prod_lt_top fun _ _ => lintegral_dom_lt_top

end GlobalTheory.IntBall.Fin3
end

