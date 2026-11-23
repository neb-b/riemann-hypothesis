module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardForms
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardRepsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsCard

theorem card_reps_eq : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ → ∀ SA SB : Finset V, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) SA → Formalism.L2.Th1.H.IsReps Λ B SB → SA.card = SB.card := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, h5⟩ := hyp
  have hBint := (Formalism.L2.Th1.H.semicharacterBasic V H hH B α hB).2.2
  have hΛint := (Formalism.L2.Th1.H.semicharacterBasic V H hH Λ α hΛ).2.2
  have hone : ∀ {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (c : ℂ), Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S →
      ∑ x ∈ S, (if x ∈ Λ₁ then c else 0) = c := by
    intro Λ₁ Λ₂ S c hS
    obtain ⟨x₀, hx₀, hd⟩ := hS.2.2 0 Λ₂.zero_mem
    have hx₀Λ : x₀ ∈ Λ₁ := by simpa using Λ₁.neg_mem hd
    rw [Finset.sum_eq_single x₀]
    · simp [hx₀Λ]
    · intro x hx hne
      rw [if_neg]
      intro hxΛ
      exact hne (hS.2.1 x hx x₀ hx₀ (Λ₁.sub_mem hxΛ hx₀Λ))
    · intro h; exact absurd hx₀ h
  have hcol : ∀ s ∈ SA, ∑ y ∈ SB, brk H y s = if s ∈ B then (SB.card : ℂ) else 0 := by
    intro s hs
    have hsΛ : s ∈ Λ := (hSA.1 s hs).1
    split_ifs with hsB
    · have hsd : s ∈ Formalism.L2.Th1.H.dualLat H B := by rw [sdB]; exact hsB
      rw [Finset.sum_congr rfl fun y hy => brk_one_of_int H (hsd y (hSB.1 y hy))]
      simp
    · by_contra hne
      apply hsB
      have hsd : s ∈ Formalism.L2.Th1.H.dualLat H B := by
        intro y hyB
        by_contra hno
        refine hne (char_sum_zero hSB (fun y => brk H y s) (fun u v => brk_add_left H u v s) ?_ (x₀ := y) hyB ?_)
        · intro m _ hmΛ; exact brk_one_of_int H (hΛint hsΛ m hmΛ)
        · intro h1; exact hno (int_of_brk_one H h1)
      rwa [sdB] at hsd
  have hrow : ∀ y ∈ SB, ∑ s ∈ SA, brk H y s = if y ∈ Λ then (SA.card : ℂ) else 0 := by
    intro y hy
    have hyB : y ∈ B := hSB.1 y hy
    split_ifs with hyΛ
    · rw [Finset.sum_congr rfl fun s hs => brk_one_of_int H (hΛint (hSA.1 s hs).1 y hyΛ)]
      simp
    · by_contra hne
      apply hyΛ
      apply h5 y hyB
      intro a haA haΛ
      by_contra hno
      refine hne (char_sum_zero hSA (fun s => brk H y s) (fun u v => brk_add_right H y u v) ?_ (x₀ := a) ⟨haΛ, haA⟩ ?_)
      · intro m _ hmB; exact brk_one_of_int H (hBint hmB y hyB)
      · intro h1; exact hno (int_of_brk_one H h1)
  have key : ∑ s ∈ SA, ∑ y ∈ SB, brk H y s = ∑ y ∈ SB, ∑ s ∈ SA, brk H y s := Finset.sum_comm
  rw [Finset.sum_congr rfl hcol, Finset.sum_congr rfl hrow, hone _ hSA, hone _ hSB] at key
  exact_mod_cast key.symm

end GlobalTheory.RepsCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharSymplOHConjHalfRest
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfCocycle

variable {D : D7} {S T : HSp D}

theorem comm4 {R : Type} [CommRing R] (c a h H : R) : c * (a * h * H) = c * a * H * h := by ring

theorem split_half {E R : Type} [Field E] [CharZero E] [CommRing R] (f : E →+* R) (x k : R) :
    x * k = x * (k * f ((2 : ℕ) : E)⁻¹) + x * (k * f ((2 : ℕ) : E)⁻¹) := by
  have h : f ((2 : ℕ) : E)⁻¹ * (1 + 1) = 1 := by
    rw [← map_one f, ← map_add (f := _), ← map_mul]
    congr 1
    norm_num
  linear_combination (-(x * k)) * h

theorem half_add {F R : Type} [Field F] [CharZero F] [CommRing R] (g : F →+* R) (t : R) :
    g (1 / 2) * (t + t) = t := by
  have h : g (1 / 2) * (1 + 1) = 1 := by
    rw [← map_one g, ← map_add (f := _), ← map_mul]
    congr 1
    norm_num
  linear_combination t * h

theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  have h := GlobalTheory.LatVacSign.hO_smul_smul 1 a x y
  rwa [one_smul, one_mul] at h

theorem hO_nsmul_right (n : ℕ) (x y : WO S T) : hO S T x (n • y) = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hO_nsmul_left (n : ℕ) (x y : WO S T) : hO S T (n • x) y = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring


set_option maxHeartbeats 1000000 in
theorem char_symplOH_conjHalf_rest : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, (2 : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : ℕ), 0 < c → ∀ (Y Z : WO S T), c • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → Z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → e • Y = c • (e • Z) → ψ (symplOH S T (cA D e • Y) ((1 - cA D e) • Y)) = 1 := by
  intro D ψ S T ΛS ΛT hψ hS hT e SS he h2 c hc Y Z hY hZ heq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D (cA D e) = e := GlobalTheory.LatVac.cA_cA e
  have hP : ∀ PP ∈ SS, ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP
    rw [Nat.cast_ofNat]
    exact h2 PP hPP
  have hint : finPart D (e * incA D ((2 : ℕ) : D.host.E)⁻¹) ∈ intAE D :=
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.DatumFourier.idem_div_int he two_ne_zero hP)
  have hZ' := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint Z hZ
  have hcA2 : cA D (incA D ((2 : ℕ) : D.host.E)⁻¹) = incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    change incA D (star ((2 : ℕ) : D.host.E)⁻¹) = _
    rw [star_inv₀, star_natCast]
  have k1 : hO S T (cA D e • Y) ((1 - cA D e) • Y) = (c : AE D) * cA D e * hO S T Y Z := by
    have a1 := GlobalTheory.LatVacSign.hO_smul_smul (cA D e) (1 - cA D e) Y Y
    have a2 := hO_smul_right e Y Y
    rw [heq, hO_nsmul_right, hO_smul_right] at a2
    rw [a1, map_sub, map_one, hcc]
    have : cA D e * (1 - e) = cA D e := by
      rw [mul_sub, mul_one, mul_comm, hec, sub_zero]
    rw [this, mul_assoc, ← a2]
  have k2 : hO S T (c • Y) ((e * incA D ((2 : ℕ) : D.host.E)⁻¹) • Z) =
      (c : AE D) * cA D e * hO S T Y Z * incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    rw [hO_nsmul_left, hO_smul_right, map_mul, hcA2]
    exact comm4 _ _ _ _
  rw [symplOH, symplO, k1, split_half (incA D) (incA D D.host.xi0) ((c : AE D) * cA D e * hO S T Y Z), map_add (f := _),
    half_add (algebraMap D.host.F (AF D.host.F)), ← k2]
  exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hY hZ'

end GlobalTheory.ConjHalfCocycle

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KLat

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev IA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem inclE_mem_IA (r : 𝓞 E) : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (r : E) ∈ IA F E :=
  Subring.subset_closure (Or.inl ⟨⟨(r : E), ⟨r, rfl⟩⟩, rfl⟩)

theorem sigR_mem_IA (σ : E →ₐ[F] E) {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (hy : y ∈ IA F E) :
    Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ IA F E := by
  have h : IA F E ≤ (IA F E).comap (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨⟨x, ⟨r, rfl⟩⟩, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
    · have hi : IsIntegral ℤ (σ (algebraMap (𝓞 E) E r)) :=
        (NumberField.RingOfIntegers.isIntegral_coe r).map (RingHom.toIntAlgHom (σ : E →+* E))
      have e : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) =
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((⟨_, hi⟩ : 𝓞 E) : E)) := rfl
      show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ IA F E
      rw [e]
      exact inclE_mem_IA (F := F) (⟨_, hi⟩ : 𝓞 E)
    · have e : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F)) = (1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F) := by
        simp [Formalism.UG.sigR]
      show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F)) ∈ IA F E
      rw [e]
      exact Subring.subset_closure (Or.inr ⟨⟨w, hw⟩, rfl⟩)
  exact h hy

variable {n : ℕ}

def HatP (π : 𝓞 E) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) : Prop :=
  ∀ j : Fin n, x j ∈ IA F E ∧
    (j.1 + 1 = n → ∃ s ∈ IA F E, x j = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((π : 𝓞 E) : E) * s)

theorem hatP_of_mem (π : 𝓞 E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L → ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    {x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (IA F E) L) : HatP π x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    intro j
    obtain ⟨r, hr, hd⟩ := hL z hz j
    refine ⟨by simp only [hr]; exact inclE_mem_IA r, fun hj => ?_⟩
    obtain ⟨t, rfl⟩ := hd hj
    refine ⟨_, inclE_mem_IA t, ?_⟩
    show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z j) = _
    rw [hr, ← map_mul]; rfl
  | zero => intro j; exact ⟨zero_mem _, fun _ => ⟨0, zero_mem _, by simp⟩⟩
  | add x y _ _ hx hy =>
    intro j
    obtain ⟨a1, a2⟩ := hx j
    obtain ⟨b1, b2⟩ := hy j
    refine ⟨add_mem a1 b1, fun hj => ?_⟩
    obtain ⟨s, hs, e⟩ := a2 hj
    obtain ⟨s', hs', e'⟩ := b2 hj
    exact ⟨s + s', add_mem hs hs', by simp only [Pi.add_apply, e, e', mul_add]⟩
  | smul c x _ hx =>
    intro j
    obtain ⟨a1, a2⟩ := hx j
    have ec : (c • x) j = (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * x j := rfl
    refine ⟨by rw [ec]; exact mul_mem c.2 a1, fun hj => ?_⟩
    obtain ⟨s, hs, e⟩ := a2 hj
    exact ⟨(c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s, mul_mem c.2 hs, by rw [ec, e]; ring⟩

end Gen

end GlobalTheory.KLat

namespace GlobalTheory.KLat

section Lev
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem inv_eq_cT {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) (lev : StepLevel F E σ J T f bad)
    {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (a b : Fin n) :
    (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 a b = Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) (g.1 b a) := by
  have hu := ((lev.U_eq g).1 hg).1
  have h : Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 * (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) * g.1 =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hu
  rw [hJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
  have e : (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 = Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 := by
    calc (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1
        = (Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 * g.1) * (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 := by
          rw [h, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e]
  rfl

variable (π : 𝓞 E) {J : Matrix (Fin n) (Fin n) E} (lev : StepLevel F E σ J T f bad)
  (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))

include hLb in
theorem img_hatP {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (y : Fin n → E) (hy : y ∈ lev.Lb) :
    HatP π (g.1 *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i)) :=
  hatP_of_mem π lev.Lb (fun x hx => (hLb x).1 hx)
    ((GlobalTheory.Mem.Col2.SameOff.stepLevel_stab lev g hg _).1 (Submodule.subset_span ⟨y, hy, rfl⟩))

theorem incl_single (j : Fin n) (c : E) :
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j c : Fin n → E) i)) =
      Pi.single j (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) c) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi]


include hLb in
theorem col_mem {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (j : Fin n) (hj : ¬ j.1 + 1 = n)
    (a : Fin n) : g.1 a j ∈ IA F E := by
  have hy : (Pi.single j 1 : Fin n → E) ∈ lev.Lb := by
    refine (hLb _).2 fun k => ?_
    by_cases hk : k = j
    · subst hk; exact ⟨1, by simp, fun h => absurd h hj⟩
    · exact ⟨0, by simp [hk], fun _ => dvd_zero _⟩
  have h := (img_hatP π lev hLb hg _ hy a).1
  rw [incl_single, map_one, Matrix.mulVec_single_one] at h
  simpa using h

include hLb in
theorem pi_ne_zero (l : Fin n) (hl : l.1 + 1 = n) : π ≠ 0 := by
  intro h0
  have hsub : (lev.Lb : Set (Fin n → E)) ⊆ (LinearMap.ker (LinearMap.proj l : (Fin n → E) →ₗ[E] E) : Set (Fin n → E)) := by
    intro x hx
    obtain ⟨r, hr, hd⟩ := (hLb x).1 hx l
    have hr0 : r = 0 := by rw [h0] at hd; exact zero_dvd_iff.1 (hd hl)
    simp [LinearMap.mem_ker, hr, hr0]
  have h2 := Submodule.span_le.2 hsub
  rw [lev.Lb_span, top_le_iff] at h2
  have h1 : (Pi.single l 1 : Fin n → E) ∈ LinearMap.ker (LinearMap.proj l : (Fin n → E) →ₗ[E] E) := by
    rw [h2]; trivial
  simp at h1


include hLb in
theorem last_mem {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (l : Fin n) (hl : l.1 + 1 = n) :
    g.1 l l ∈ IA F E := by
  have hy : (Pi.single l (π : E) : Fin n → E) ∈ lev.Lb := by
    refine (hLb _).2 fun k => ?_
    by_cases hk : k = l
    · subst hk; exact ⟨π, by simp, fun _ => dvd_rfl⟩
    · exact ⟨0, by simp [hk], fun _ => dvd_zero _⟩
  obtain ⟨s, hs, e⟩ := (img_hatP π lev hLb hg _ hy l).2 hl
  rw [incl_single, Matrix.mulVec_single] at e
  have hπ : (π : E) ≠ 0 := fun h => pi_ne_zero π lev hLb l hl (by exact_mod_cast h)
  have hu : IsUnit (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E)) := (IsUnit.mk0 _ hπ).map _
  have e2 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E) * g.1 l l = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E) * s := by
    rw [mul_comm]; exact e
  rw [hu.mul_left_cancel e2]
  exact hs


include hLb in
theorem entry_mem (hJ : J = 1) {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (a b : Fin n) :
    g.1 a b ∈ IA F E := by
  by_cases hb : b.1 + 1 = n
  · by_cases ha : a.1 + 1 = n
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      exact last_mem π lev hLb hg a ha
    · have hi : g⁻¹ ∈ lev.U := inv_mem hg
      have e := inv_eq_cT hJ lev hi a b
      rw [inv_inv] at e
      rw [e]
      exact sigR_mem_IA σ (col_mem π lev hLb hi a ha b)
  · exact col_mem π lev hLb hg b hb a

theorem entry_memD {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (π : 𝓞 D.host.E) (lev : StepLevel D.host.F D.host.E (sigD D) J T f bad)
    (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → π ∣ r))
    (hJ : J = 1) {g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)} (hg : g ∈ lev.U) (a b : Fin n) :
    g.1 a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  entry_mem π lev hLb hJ hg a b

end Lev

end GlobalTheory.KLat

namespace GlobalTheory.AdForm

theorem levels_keep_stdLat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  intro B X I hI _ l Z u a Ch A hA i hi β k hk
  obtain ⟨-, κ, hκ⟩ := (hA.U i hi β k).1 hk
  have hV : ((I.rec7 l Z).sp.X i).gram = 1 := hI.gram_X i
  refine GlobalTheory.SplitDec.moves_std hV _ ?_
  have hJ : gramN (I.rec7 l Z) i hi = 1 := by
    unfold gramN
    rw [hV]
    simp
  have hLb := (hA.reads i hi).lb β
  intro p q
  have e : toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ k p q) =
      finM _ (rankN (I.rec7 l Z) i hi) k (finCongr (rankN _ i hi) p) (finCongr (rankN _ i hi) q) := by
    simp [finM, Matrix.reindex_apply]
  rw [e, ← hκ]
  have hLb' : ∀ x, x ∈ (A.K i hi β).lev.Lb ↔ ∀ j : Fin ((I.rec7 l Z).R.N i), ∃ r : 𝓞 (I.rec7 l Z).host.E,
      x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = (I.rec7 l Z).R.N i → (X.piT u : 𝓞 (I.rec7 l Z).host.E) ∣ r) :=
    fun x => hLb x
  exact GlobalTheory.KLat.entry_memD _ (A.K i hi β).lev hLb' hJ κ.2 _ _

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPEqCP
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemDen
open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem conjP_eq_cP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ Q = cP Q :=
  HeightOneSpectrum.ext (Ideal.ext fun _ => Iff.rfl)

def evQ (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E where
  toFun z := Φ z Q
  map_one' := by rw [map_one]; rfl
  map_mul' a b := ev_mul a b Q
  map_zero' := ev_zero Q
  map_add' a b := ev_add a b Q

theorem delta_mem {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)}
    {x : AE D} (h : IsDelta Φ P x) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ x Q ∈ Q.adicCompletionIntegers D.host.E := by
  by_cases hQ : Q = P
  · subst hQ; rw [h.2.1]; exact (Q.adicCompletionIntegers D.host.E).one_mem
  · rw [h.2.2 Q hQ]; exact (Q.adicCompletionIntegers D.host.E).zero_mem

end GlobalTheory.OffIdemDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriods
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem perLaw_holds : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (Y : Formalism.L2.SG.Full.Full X), IsStdChar D ψ (-1) → InHH X u Y.hK → B.PerLaw Y := by
  intro D X h u ψ A B Y hψ hH
  obtain ⟨Fs, hFs⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratFund_holds X u
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.Core.Mi.unfoldedPer D X h u ψ A B Y.hK hψ Fs hFs
  refine ⟨c, fun T f φ hf hφ => ?_⟩
  rw [_root_.GlobalTheory.Core.Mi.inner_pser_eq_setIntegral D X u Y.hK (Y.Dt u) Fs (Y.reps u) hH hFs T (hc T).1 f φ hf hφ]
  exact (hc T).2 f hf

end GlobalTheory.Core.Mi
end

