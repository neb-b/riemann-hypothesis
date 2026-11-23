module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrigPolynomialIndicatorAwayFromPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.OffVTrig

variable {F : Type} [Field F] [NumberField F]

abbrev ev1 (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Af F := GlobalTheory.AdelicU.singleFin v 1

abbrev gv (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Af F := 1 - ev1 v

theorem finiteAdeleIndicatorAtPlace_mul_self (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : ev1 v * ev1 v = ev1 v := by
  rw [ev1, ← GlobalTheory.AdelicU.singleFin_mul, mul_one]

theorem finiteAdeleIndicatorAtPlace_mul_awayFromPlace (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : ev1 v * gv v = 0 := by
  rw [gv, mul_sub, mul_one, finiteAdeleIndicatorAtPlace_mul_self, sub_self]

variable {κ : Type} [Fintype κ]

def offV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (u : κ → Af F) : κ → Af F := fun i => gv v * u i

theorem continuous_offV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Continuous (offV (κ := κ) v) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

theorem vecFin_sub (u u' : κ → Af F) :
    GlobalTheory.FinTrig.vecFin (u - u') = GlobalTheory.FinTrig.vecFin u - GlobalTheory.FinTrig.vecFin u' := by
  funext i
  exact Prod.ext (show (0 : InfiniteAdeleRing F) = 0 - 0 by rw [sub_zero]) rfl

theorem exists_lev_subset (y : κ → Af F) (V : Set (κ → Af F)) (hV : IsOpen V) (hy : y ∈ V) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ {u | GlobalTheory.FinTrig.Lev d (u - y)} ⊆ V := by
  have h1 : (fun z : κ → Af F => y + z) ⁻¹' V ∈ nhds (0 : κ → Af F) :=
    (hV.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hy)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, _, t, ht, hsub⟩ := h1
  have hW : (⋂ i, t i) ∈ nhds (0 : Af F) := Filter.iInter_mem.mpr fun i => ht i
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => ?_⟩
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd0
  have hmem : ∀ i, u i - y i ∈ ⋂ j, t j := by
    intro i
    have e : u i - y i = algebraMap F (Af F) (algebraMap (𝓞 F) F d) *
        (algebraMap F (Af F) ((d : F)⁻¹) * (u i - y i)) := by
      rw [← mul_assoc, ← map_mul]
      change _ = algebraMap F (Af F) ((d : F) * (d : F)⁻¹) * _
      rw [mul_inv_cancel₀ hd', map_one, one_mul]
    rw [e]; exact hd _ (hu i)
  have : (fun z : κ → Af F => y + z) (u - y) ∈ V := hsub (fun i _ => Set.mem_iInter.mp (hmem i) i)
  simpa using this

def Freq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Set (κ → AF F) := {b | ∀ i, (b i).1 = 0 ∧ ev1 v * (b i).2 = 0}

theorem zero_mem_freq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : (0 : κ → AF F) ∈ Freq v := fun i =>
  ⟨rfl, show ev1 v * (0 : Af F) = 0 from mul_zero _⟩

theorem add_mem_freq {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {b b' : κ → AF F} (h : b ∈ Freq v) (h' : b' ∈ Freq v) :
    b + b' ∈ Freq v := fun i =>
  ⟨show (b i).1 + (b' i).1 = 0 by rw [(h i).1, (h' i).1, add_zero],
    show ev1 v * ((b i).2 + (b' i).2) = 0 by rw [mul_add, (h i).2, (h' i).2, add_zero]⟩

def TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Submodule ℂ ((κ → AF F) → ℂ) :=
  Submodule.span ℂ (GlobalTheory.FinTrig.chi ψ '' (Freq v))

theorem chi_mem_TPv (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {b : κ → AF F} (hb : b ∈ Freq v) :
    GlobalTheory.FinTrig.chi ψ b ∈ TPv ψ v :=
  Submodule.subset_span ⟨b, hb, rfl⟩

theorem one_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : (1 : (κ → AF F) → ℂ) ∈ TPv ψ v := by
  rw [← GlobalTheory.FinTrig.chi_zero ψ]; exact chi_mem_TPv ψ (zero_mem_freq v)

theorem mul_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {f g : (κ → AF F) → ℂ}
    (hf : f ∈ TPv ψ v) (hg : g ∈ TPv ψ v) : f * g ∈ TPv ψ v := by
  have hle : TPv ψ v * TPv ψ v ≤ TPv (κ := κ) ψ v := by
    rw [TPv, Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨q, hq, rfl⟩, b, ⟨q', hq', rfl⟩, rfl⟩
    exact ⟨q + q', add_mem_freq hq hq', (GlobalTheory.FinTrig.chi_mul ψ q q').symm⟩
  exact hle (Submodule.mul_mem_mul hf hg)

theorem prod_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {ι : Type} (t : Finset ι)
    (f : ι → (κ → AF F) → ℂ) (h : ∀ a ∈ t, f a ∈ TPv ψ v) : (∏ a ∈ t, f a) ∈ TPv ψ v :=
  Finset.prod_induction f (· ∈ TPv ψ v) (fun _ _ => mul_mem_TPv ψ v) (one_mem_TPv ψ v) h

theorem exists_of_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {P : (κ → AF F) → ℂ}
    (h : P ∈ TPv ψ v) :
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, q ∈ Freq v) ∧
      ∀ x, P x = ∑ q ∈ s, c q * ψ (x ⬝ᵥ q) := by
  rw [TPv, Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, rfl⟩ := h
  refine ⟨l.support, l, fun q hq => (Finsupp.mem_supported ℂ l).1 hl hq, fun x => ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  rfl

def killV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q : κ → AF F) : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), gv v * (q i).2)

theorem killV_mem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q : κ → AF F) : killV v q ∈ Freq v := fun i =>
  ⟨rfl, show ev1 v * (gv v * (q i).2) = 0 by rw [← mul_assoc, finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]⟩

theorem dot_killV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q x : κ → AF F) :
    x ⬝ᵥ killV v q = GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2)) ⬝ᵥ q := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => Prod.ext ?_ ?_
  · show (x i).1 * 0 = 0 * (q i).1
    rw [mul_zero, zero_mul]
  · show (x i).2 * (gv v * (q i).2) = (gv v * (x i).2) * (q i).2
    ring

end GlobalTheory.OffVTrig

namespace GlobalTheory.OffVTrig

theorem exists_offV_indicator_poly : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  intro F _ _ κ _ v ψ hψ _ K hK y V hV hyV
  classical
  obtain ⟨d, -, hdV⟩ := exists_lev_subset (fun i => (y i).2) V hV hyV
  have hPc := continuous_offV (κ := κ) v
  have hAo : IsOpen {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} :=
    (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).preimage hPc
  set C := offV v '' K ∩ {z | GlobalTheory.FinTrig.Lev d (z - offV v (fun i => (y i).2))}ᶜ with hCdef
  have hC : IsCompact C :=
    (hK.image hPc).inter_right (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun a => {z | GlobalTheory.FinTrig.Lev d (z - a)})
    (fun a _ => (GlobalTheory.FinTrig.isOpen_lev d a).mem_nhds
      (by simp only [Set.mem_setOf_eq, sub_self]; exact GlobalTheory.FinTrig.lev_zero d))
  have hsep : ∀ a ∈ C, ∃ q ∈ (GlobalTheory.FinTrig.Q0 : Set (κ → AF F)),
      ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, GlobalTheory.FinTrig.Lev d u → ψ (GlobalTheory.FinTrig.vecFin u ⬝ᵥ q) = 1 :=
    fun a ha => GlobalTheory.FinTrig.exists_sep ψ hψ d (a - offV v (fun i => (y i).2)) ha.2
  choose! q _ hq1 hq2 using hsep
  set c : (κ → Af F) → ℂ := fun a => ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q a) with hc
  set φ : (κ → Af F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) •
      GlobalTheory.FinTrig.chi ψ (killV v (q a)) - c a • 1) with hφ
  have hφx : ∀ a x, φ a x = (1 - c a)⁻¹ *
      (ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) - c a) := by
    intro a x
    have e1 : ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) * ψ (x ⬝ᵥ killV v (q a)) =
        ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, dot_killV, vecFin_sub, sub_dotProduct, neg_add_eq_sub]
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, GlobalTheory.FinTrig.chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TPv ψ v := fun a _ =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem_TPv ψ (killV_mem v (q a))))
      (Submodule.smul_mem _ _ (one_mem_TPv ψ v)))
  obtain ⟨s, cc, hs, hPs⟩ := exists_of_mem_TPv ψ v (prod_mem_TPv ψ v t φ hφmem)
  refine ⟨{u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))}, s, cc, hAo, ?_, ?_, ?_, ?_, ?_⟩
  · show GlobalTheory.FinTrig.Lev d (offV v (fun i => (y i).2) - offV v (fun i => (y i).2))
    rw [sub_self]; exact GlobalTheory.FinTrig.lev_zero d
  · intro b hb
    funext i
    exact Prod.ext (show (0 : InfiniteAdeleRing F) * (b i).1 = 0 from zero_mul _)
      (show ev1 v * (b i).2 = 0 from (hs b hb i).2)
  · intro x z hz
    have hz2 : ∀ i, gv v * (z i).2 = 0 := by
      intro i
      have h1 : ((GlobalTheory.LatVac.liftV v 1 • z) i).2 = ev1 v * (z i).2 := rfl
      rw [hz] at h1
      rw [h1, ← mul_assoc, mul_comm (gv v), finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]
    have e : offV v (fun i => ((x + z) i).2) = offV v (fun i => (x i).2) := by
      funext i
      show gv v * ((x i).2 + (z i).2) = gv v * (x i).2
      rw [mul_add, hz2 i, add_zero]
    show GlobalTheory.FinTrig.Lev d (offV v _ - _) ↔ GlobalTheory.FinTrig.Lev d (offV v _ - _)
    rw [e]
  · intro x hx
    apply hdV
    show GlobalTheory.FinTrig.Lev d (_ - _)
    have e : (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) - (fun i => (y i).2) =
        offV v (fun i => (x i).2) - offV v (fun i => (y i).2) := by
      funext i
      show (x i).2 + (ev1 v * (y i).2 - ev1 v * (x i).2) - (y i).2 = gv v * (x i).2 - gv v * (y i).2
      simp only [gv]; ring
    rw [e]; exact hx
  · intro x hxK
    rw [← hPs x, Finset.prod_apply]
    by_cases hxA : GlobalTheory.FinTrig.Lev d (offV v (fun i => (x i).2) - offV v (fun i => (y i).2))
    · rw [Set.indicator_of_mem (show (fun i => (x i).2) ∈
          {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]
      refine Finset.prod_eq_one fun a ha => ?_
      rw [hφx a x, hq2 a (htC a ha) _ hxA]
      have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
      exact inv_mul_cancel₀ hne
    · rw [Set.indicator_of_notMem (show (fun i => (x i).2) ∉
          {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]
      have hxC : offV v (fun i => (x i).2) ∈ C := ⟨⟨_, hxK, rfl⟩, hxA⟩
      obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC)
      refine Finset.prod_eq_zero hat ?_
      rw [hφx a x]
      have e : offV v (fun i => (x i).2) - offV v (fun i => (y i).2) =
          (offV v (fun i => (x i).2) - a) + (a - offV v (fun i => (y i).2)) := (sub_add_sub_cancel _ _ _).symm
      rw [e, GlobalTheory.FinTrig.vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul,
        sub_self, mul_zero]

end GlobalTheory.OffVTrig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.IoExtPf

section Rep

open Formalism.MainNotions.S

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_ext_mem (hU : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε σ Λ S) :
    ∃ w ∈ S, ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Λ (revNeg ε a)) w := by
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖ := hU.2.1 _ (kset_uj hK) v
  have hp : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, ?_, ?_, isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩
  · exact Submodule.smul_mem _ _ (hS.2.1 _ hK v hvS)
  · rw [norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]

theorem lowK_irred (hσ : IsDS ε lam σ)
    (hl : ∀ w w' : H, ‖w‖ = 1 → w ∈ lowKSub ε lam σ →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w → ‖w'‖ = 1 → w' ∈ lowKSub ε lam σ →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w' → ∃ c : ℂ, w' = c • w)
    (N : Submodule ℂ H) (hN : N ≤ lowKSub ε lam σ) (hst : IsKStableOn ε σ N) : N = ⊥ ∨ N = lowKSub ε lam σ := by
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := hσ
  have hle : ∀ S', IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S' ≤ lowKSub ε lam σ := fun S' h =>
    le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) h
  have key : lowKSub ε lam σ = S := by
    refine le_antisymm (sSup_le fun S' hS' => ?_) (hle S hS)
    obtain ⟨w, hw, hw1, hwt⟩ := exists_ext_mem hU hS
    obtain ⟨w', hw', hw1', hwt'⟩ := exists_ext_mem hU hS'
    obtain ⟨c, hc⟩ := hl w w' hw1 (hle S hS hw) hwt hw1' (hle S' hS' hw') hwt'
    have hm : w' ∈ S' ⊓ S := ⟨hw', hc ▸ S.smul_mem c hw⟩
    rcases hS'.2.2.1 (S' ⊓ S) inf_le_left (fun g hg v hv => ⟨hS'.2.1 g hg v hv.1, hS.2.1 g hg v hv.2⟩) with h | h
    · rw [h, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw1'
      exact absurd hw1' zero_ne_one
    · exact h ▸ inf_le_right
  rw [key] at hN ⊢
  exact hS.2.2.1 N hN hst

end Rep

section Minors

variable {D : D7} {m n : ℕ}

theorem minor_ne (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.2
    have hβ := β.2
    have hr : a + β < m ∧ b + α < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos hr, MvPolynomial.eval_X,
      Matrix.one_apply, Fin.ext_iff]
    exact if_congr ⟨fun h => by omega, fun h => by omega⟩ rfl rfl
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem delta_ne (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta deltaAt
  refine Finset.prod_ne_zero_iff.2 fun τ _ => mul_ne_zero
    (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_)
  · have := Finset.mem_range.1 hi
    have := hpq τ
    have h := minor_ne (m := m) (n := n) τ 0 0 (i + 1) (by omega) (by omega)
    simpa only [minorPlus, zero_add] using h
  · have := Finset.mem_range.1 hi
    have := hpq τ
    exact minor_ne (m := m) (n := n) τ (p τ) (n - (i + 1)) (i + 1) (by omega) (by omega)

theorem Delta_ne (i : Fin D.R.m) : RealDat.Delta (D := D) i ≠ 0 := by
  refine delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))
  rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]
  have := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

end Minors

section Io

open Formalism.MainNotions.S Formalism.IndefR.Mult

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel W S)

theorem model_irred (hs : LowSm M) (hl : ExtLine M) (τ : D.what₂.Tau) (N : Submodule ℂ (M.H τ))
    (hN : N ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) (hst : IsKStableOn (M.ε τ) (M.σ τ) N) :
    N = ⊥ ∨ N = lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := by
  refine lowK_irred (M.ds τ) (fun w w' h1 h2 h3 h1' h2' h3' => ?_) N hN hst
  obtain ⟨e, he⟩ := exists_isExtVec M hs
  have hu : ∀ (x : M.sm τ), ‖(x : M.H τ)‖ = 1 → (x : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) →
      IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (x : M.H τ) → IsExtVec M (Function.update e τ x) := by
    intro x a b c ρ
    by_cases h : ρ = τ
    · subst h
      rw [Function.update_self]
      exact ⟨a, b, c⟩
    · rw [Function.update_of_ne h]
      exact he ρ
  obtain ⟨c, -, hc⟩ := hl _ _ (hu ⟨w, hs τ h2⟩ h1 h2 h3) (hu ⟨w', hs τ h2'⟩ h1' h2' h3') τ
  rw [Function.update_self, Function.update_self] at hc
  exact ⟨c, congrArg Subtype.val hc⟩

theorem inj_factor (hs : LowSm M) (hl : ExtLine M) (τ : D.what₂.Tau) {X : Type} [AddCommGroup X] [Module ℂ X]
    (f : LowT M →ₗ[ℂ] X) (om : Matrix (Fin W.rank) (Fin W.rank) ℂ → X →ₗ[ℂ] X)
    (hf : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) →
      om k (f (PiTensorProduct.tprod ℂ v)) = f (PiTensorProduct.tprod ℂ (Function.update v τ u)))
    (v : ∀ ρ, lowT M ρ) (hv : f (PiTensorProduct.tprod ℂ v) ≠ 0) (x : lowT M τ)
    (hx : f (PiTensorProduct.tprod ℂ (Function.update v τ x)) = 0) : x = 0 := by
  let g : lowT M τ →ₗ[ℂ] X := f ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
  have hg : ∀ y, g y = f (PiTensorProduct.tprod ℂ (Function.update v τ y)) := fun y => rfl
  let j : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hst := GlobalTheory.LowKProj.lowKSub_stable (M.ε τ) (M.lam τ) (M.σ τ)
  rcases model_irred M hs hl τ ((LinearMap.ker g).map j) (by rintro _ ⟨y, -, rfl⟩; exact y.2) (by
      rintro k hk _ ⟨y, hy, rfl⟩
      have hm : M.σ τ k (j y) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := hst k hk _ y.2
      refine ⟨⟨⟨_, hs τ hm⟩, hm⟩, ?_, rfl⟩
      have := hf k hk (Function.update v τ y) ⟨⟨_, hs τ hm⟩, hm⟩ (by rw [Function.update_self]; rfl)
      rw [Function.update_idem, ← hg, ← hg, (LinearMap.mem_ker.1 hy : g y = 0), map_zero] at this
      exact this.symm) with h | h
  · have : j x ∈ (LinearMap.ker g).map j := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hj (this.trans (map_zero j).symm)
  · have : j (v τ) ∈ (LinearMap.ker g).map j := by rw [h]; exact (v τ).2
    obtain ⟨y, hy, hy'⟩ := this
    rw [hj hy'] at hy
    have h0 : g (v τ) = 0 := hy
    rw [hg, Function.update_eq_self] at h0
    exact absurd h0 hv

end Io

end GlobalTheory.AdTh.IoExtPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacKInf.LeviFix

variable {D : D7}

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_adj' {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (x : Mx D m n) :
    compAt θ τ (adj x) = (compAt θ τ x)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.FockCompare.comp_cA hθ τ]
  rfl

end GlobalTheory.VacKInf.LeviFix

namespace GlobalTheory.VacKInf

end GlobalTheory.VacKInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGrids
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SquareInfGap

theorem square_infExp_gap : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro _ i j
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := by
    show (G.V (.grid (i : ℕ) (j : ℕ))).rank % 2 = _
    rw [(node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).rank]
    rfl
  refine ⟨fun τ => -(D.hc τ).e ⟨j, j.2⟩ + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2),
    fun τ => (cen D 1 τ (D.R.m - i) : ℚ) + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2), fun t τ => ⟨?_, ?_, ?_⟩⟩
  · have h := GlobalTheory.SquareExps.alpha_exp (G := G) hL t i j j.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, hε] at h
    exact h
  · have h := GlobalTheory.SquareExps.beta_exp (G := G) hL i j i.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps] at h
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps, hε] at h
    exact h
  · have key := GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen (D := D) 1 τ i j i.2 j.2
    push_cast at key ⊢
    linarith

end GlobalTheory.SquareInfGap

end
end

