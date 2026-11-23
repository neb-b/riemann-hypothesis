module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOfMemPartW
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableContAut

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductOverPlacesCompactOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinGrp

open GlobalTheory.FinPl

theorem map_ofFn_prod_eq {G M : Type*} [Group G] [Monoid M] (φ : G →* M) :
    ∀ {r : ℕ} (a : Fin r → G) (i : Fin r), (∀ j, j ≠ i → φ (a j) = 1) → φ (List.ofFn a).prod = φ (a i)
  | 0, _, i, _ => i.elim0
  | r + 1, a, i, h => by
    rw [List.ofFn_succ, List.prod_cons, φ.map_mul]
    cases i using Fin.cases with
    | zero =>
      have h1 : φ (List.ofFn fun j : Fin r => a j.succ).prod = 1 := by
        rw [φ.map_list_prod, List.map_ofFn]
        refine List.prod_eq_one (l := List.ofFn fun j : Fin r => φ (a j.succ)) ?_
        rw [List.forall_mem_ofFn_iff]
        exact fun j => h _ (Fin.succ_ne_zero j)
      rw [h1, mul_one]
    | succ i' =>
      rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact map_ofFn_prod_eq φ (fun j => a j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

variable {D : D7}

theorem loc_facts {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (i : Fin F.r) :
    GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) ∧
    IsCompact (GlobalTheory.QuotientFiniteLevel.locK F j σ h i : Set (GA D (c.V (j + 1)))) ∧
    IsOpen {x : grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) |
      (x : GA D (c.V (j + 1))) ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i} := by
  have hd : j + 1 + ((F.Q i).s - j) = (F.Q i).s + 1 := by have := (F.Q i).hs; omega
  obtain ⟨hce, hrange, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1))
    ((F.Q i).X (j + 1) ⊕ Fin ((F.Q i).s - j)) ((F.Q i).FY (j + 1) ((F.Q i).s - j) hd)
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ((F.Q i).gl_loc _ _ hd)
  have hr : ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd).range =
      grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) := by
    rw [hrange]; congr 1; funext p; exact propext Finset.mem_singleton.symm
  obtain ⟨hJo, hJc, -⟩ := (F.Q i).reg.2.2 (j + 1) ((F.Q i).s - j) hd
  refine ⟨?_, ?_, ?_⟩
  · rw [← hr]; intro x hx; obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx; exact ⟨g, rfl⟩
  · rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.coe_map]; exact hJc.image hce.continuous
  · obtain ⟨U, hU, hUe⟩ := hce.isInducing.isOpen_iff.1 hJo
    convert hU.preimage continuous_subtype_val using 1
    ext ⟨x, hx⟩
    rw [← hr] at hx
    obtain ⟨g, rfl⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.mem_map]
    constructor
    · rintro ⟨g', hg', e⟩
      have : g' ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hUe.symm ▸ hg'
      rw [← e]; exact this
    · intro hU'
      have hg : g ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hU'
      rw [hUe] at hg
      exact ⟨g, hg, rfl⟩

theorem qK_grp : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w →
    ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧
      IsCompact (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) ∧
      IsOpen (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) : Subgroup _) :
        Set (GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q))) := by
  intro D c v t w F hF j σ h
  have hloc := loc_facts F j σ h
  have hv : ∀ i, (F.Q i).q.v ∈ w.Q := fun i => (hF.places _).2 ⟨i, rfl⟩
  have hle : ∀ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := fun i => (hloc i).1.trans
    (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp => (Finset.mem_singleton.1 hp) ▸ hv i)
  have hoff : ∀ i i', i ≠ i' →
      GlobalTheory.QuotientFiniteLevel.locK F j σ h i' ≤ grpAt (c.V (j + 1)) (· ∉ ({(F.Q i).q.v} : Finset (Pl D))) := fun i i' hii' =>
    (hloc i').1.trans (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp hp' =>
      hii' (hF.inj ((Finset.mem_singleton.1 hp').symm.trans (Finset.mem_singleton.1 hp))))
  have hcomm : Pairwise fun i i' => ∀ x y : GA D (c.V (j + 1)),
      x ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i → y ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i' → Commute x y := by
    intro i i' hii' x y hx hy
    exact (GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1)) {(F.Q i).q.v}).2.2.2.2.1 x ((hloc i).1 hx) y (hoff i i' hii' hy)
  have hqK : GlobalTheory.QuotientFiniteLevel.qK F j σ h = ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i := rfl
  have hQle : GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := iSup_le hle
  refine ⟨hQle, ?_, ?_⟩
  · have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
    have hcont : Continuous (Subgroup.noncommPiCoprod hcomm) := by
      have e : ⇑(Subgroup.noncommPiCoprod hcomm) = fun x =>
          ((List.finRange F.r).map fun i => ((x i : GlobalTheory.QuotientFiniteLevel.locK F j σ h i) : GA D (c.V (j + 1)))).prod := by
        funext x
        simp [Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod, Finset.noncommProd, List.ofFn_eq_map]
      rw [e]
      exact continuous_list_prod _ fun i _ => continuous_subtype_val.comp (continuous_apply i)
    haveI : ∀ i, CompactSpace (GlobalTheory.QuotientFiniteLevel.locK F j σ h i) := fun i => isCompact_iff_compactSpace.1 (hloc i).2.1
    have : (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) = Set.range (Subgroup.noncommPiCoprod hcomm) := by
      rw [hqK, ← hrange, MonoidHom.coe_range]
    rw [this]; exact isCompact_range hcont
  · set V := c.V (j + 1) with hVdef
    set K := GlobalTheory.QuotientFiniteLevel.locK F j σ h with hKdef
    obtain ⟨-, -, hQf, -, -, ⟨eQ, heQ⟩, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V w.Q
    have hbot : ∀ a, a ∈ grpAt V (· ∈ w.Q) → a ∈ grpAt V (· ∉ w.Q) → a = 1 := by
      intro a h1 h2
      have : eQ (⟨a, h1⟩, 1) = eQ (1, ⟨a, h2⟩) := by
        apply Subtype.ext; rw [heQ, heQ]; simp
      exact congrArg (fun p => (p.1 : GA D V)) (eQ.injective this)
    choose e he using fun i => (GlobalTheory.FinPl.SetCut.grp_split D V {(F.Q i).q.v}).2.2.2.2.2.1
    have he' : ∀ i (z : GfC V), (z : GA D V) = (((e i).symm z).1 : GA D V) * (((e i).symm z).2 : GA D V) := by
      intro i z; rw [← he i, Homeomorph.apply_symm_apply]
    let ι : grpAt V (· ∈ w.Q) → GfC V := fun x => ⟨x.1, hQf x.2⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    let U : Set (grpAt V (· ∈ w.Q)) := ⋂ i, {x | ((((e i).symm (ι x)).1 : _) : GA D V) ∈ K i}
    have hUo : IsOpen U := isOpen_iInter_of_finite fun i =>
      (hloc i).2.2.preimage (continuous_fst.comp ((e i).symm.continuous.comp hι))
    have h1U : (1 : grpAt V (· ∈ w.Q)) ∈ U := by
      refine Set.mem_iInter.2 fun i => ?_
      have : (e i).symm (ι 1) = 1 := by
        rw [Homeomorph.symm_apply_eq]; apply Subtype.ext; rw [he]; simp [ι]
      show ((((e i).symm (ι 1)).1 : _) : GA D V) ∈ K i
      rw [this]; exact (K i).one_mem
    have hprj : ∀ i, ∀ b ∈ grpAt V (· ∉ ({(F.Q i).q.v} : Finset (Pl D))),
        GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v b = 1 := fun i b hb =>
      ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ b).1 hb).2 _ (by simp)
    have hUsub : U ⊆ (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (grpAt V (· ∈ w.Q)) : Subgroup _) : Set _) := by
      intro x hx
      have hx' := Set.mem_iInter.1 hx
      let a : Fin F.r → GA D V := fun i => (((e i).symm (ι x)).1 : GA D V)
      have ha : ∀ i, a i ∈ K i := fun i => hx' i
      have hp : (List.ofFn a).prod ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h := by
        refine Subgroup.list_prod_mem _ fun y hy => ?_
        rw [List.mem_ofFn] at hy
        obtain ⟨i, rfl⟩ := hy
        exact (le_iSup K i) (ha i)
      have hy1 : ∀ i, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v ((x : GA D V) * ((List.ofFn a).prod)⁻¹) = 1 := by
        intro i
        have hxi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (x : GA D V) =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) := by
          have := he' i (ι x)
          change (x : GA D V) = a i * _ at this
          rw [this, map_mul, hprj i _ (((e i).symm (ι x)).2).2, mul_one]
        have hpi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (List.ofFn a).prod =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) :=
          map_ofFn_prod_eq _ a i fun j' hj' => hprj i _ (hoff i j' (Ne.symm hj') (ha j'))
        rw [map_mul, map_inv, hxi, hpi, mul_inv_cancel]
      have hyQ : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∈ w.Q) :=
        mul_mem x.2 (inv_mem (hQle hp))
      have hyN : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∉ w.Q) := by
        refine (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ _).2 ⟨hQf hyQ, fun p hp' => ?_⟩
        obtain ⟨i, rfl⟩ := (hF.places p).1 (not_not.1 hp')
        exact hy1 i
      have hxp : (x : GA D V) = (List.ofFn a).prod := mul_inv_eq_one.1 (hbot _ hyQ hyN)
      show (x : GA D V) ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h
      rw [hxp]; exact hp
    exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hUo.mem_nhds h1U) hUsub)

end GlobalTheory.QFinGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTraceChiCol


open Classical in
def colLam {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : ℂ :=
  if h : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal then
    Formalism.L2.Forms.lamJ (T.gl.psi0 h.choose v h.choose_spec) (T.gl.chiB h.choose v h.choose_spec) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
        (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g)))
  else 1

theorem type_idx_unique {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)} {j j' : Fin 2}
    (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal) : j' = j := by
  by_contra hne
  have hg : D.host.g j' ≠ D.host.g j := by
    intro e
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> rcases Fin.exists_fin_two.mp ⟨j', rfl⟩ with hj' | hj' <;>
      subst hj hj' <;> first | exact hne rfl | exact D.host.g_ne e | exact D.host.g_ne e.symm
  have hc : Nat.Coprime (D.host.g j') (D.host.g j) := (Nat.coprime_primes (D.host.g_prime j') (D.host.g_prime j)).2 hg
  obtain ⟨a, b, hab⟩ : IsCoprime (D.host.g j' : ℤ) (D.host.g j : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (1 : 𝓞 D.host.F) ∈ v.asIdeal := by
    have e : ((a * (D.host.g j' : ℤ) + b * (D.host.g j : ℤ) : ℤ) : 𝓞 D.host.F) = 1 := by rw [hab]; simp
    rw [← e]
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h') (v.asIdeal.mul_mem_left _ h)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem colLam_eq {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)}
    (j : Fin 2) (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal)
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    colLam T v g = Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
  have hex : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := ⟨j, h⟩
  unfold colLam
  rw [dite_eq_left hex]
  have key : ∀ (j' : Fin 2) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal), j' = j →
      Formalism.L2.Forms.lamJ (T.gl.psi0 j' v h') (T.gl.chiB j' v h') D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j' v h' (T.glev0.fr j' v h') (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) =
      Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
    rintro j' h' rfl; rfl
  exact key _ _ (type_idx_unique h hex.choose_spec)

end GlobalTheory.FamTraceChiCol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem mt_mem_GQ_rat {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = rat M := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩


set_option maxHeartbeats 1000000 in
theorem unfold_over_N_lift : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ n in vN.𝓝, Th n.1 * liftS om vW.μ vW.𝓕 G Φ n.1 ∂vN.ν = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  intro D hD ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hx hTh G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨act, y₀, hy₀, hrel, htrans, hstab1, hstab2⟩ := GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer D V V₀ W ρ d x₀ hx
  letI := act
  obtain ⟨𝓐, h𝓐, hlay⟩ := _root_.GlobalTheory.Unf.layers_integral D V V₀ ρ d vN vb vU
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  haveI hΓc : Countable ((NFlagQ V d.e).prod (GQ W)) := Function.Injective.countable
    (f := fun γ : (NFlagQ V d.e).prod (GQ W) => ((⟨γ.1.1, (Subgroup.mem_prod.1 γ.2).1⟩ : NFlagQ V d.e),
      (⟨γ.1.2, (Subgroup.mem_prod.1 γ.2).2⟩ : GQ W)))
    fun a b h => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  haveI : Countable ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) :=
    (Subgroup.inclusion_injective (Subgroup.map_subtype_le (MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀))).countable
  have hF : IsFundamentalDomain ((NFlagQ V d.e).prod (GQ W)) (vN.𝓝 ×ˢ vW.𝓕) (vN.ν.prod vW.μ) := by
    refine _root_.GlobalTheory.isFundamentalDomain_prod_of_ker_image _ _ vN.ν vW.μ _ vN.𝓝 vW.𝓕 ?_ ?_
    · have hc : ((NFlagQ V d.e).prod (GQ W)).comap (MonoidHom.inl (flagN d) (GA D W)) = NFlagQ V d.e := by
        ext n
        simp only [Subgroup.mem_comap, MonoidHom.inl_apply, Subgroup.mem_prod, one_mem, and_true]
      rw [hc]; exact hN2
    · have hc : ((NFlagQ V d.e).prod (GQ W)).map (MonoidHom.snd (flagN d) (GA D W)) = GQ W := by
        ext h
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact (Subgroup.mem_prod.1 hp).2
        · intro hh
          exact ⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩, rfl⟩
      rw [hc]; exact vW.fund
  have hG' : IsFundamentalDomain ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _))
      (𝓐 ×ˢ 𝓑) (vN.ν.prod vW.μ) := by
    refine _root_.GlobalTheory.isFundamentalDomain_prod_of_ker_image _ _ vN.ν vW.μ _ 𝓐 𝓑 ?_ ?_
    · rw [hstab1]; exact h𝓐
    · rw [hstab2]; exact h𝓑
  have hmeas : ∀ y : Orb W x₀, Measurable fun p : flagN d × GA D W =>
      Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
    intro y
    have t4 := (_root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hω hω' vS Φ hΦ).2.2.2.1 y.1
    refine Continuous.measurable ?_
    refine ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul ?_
    exact t4.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hinv : ∀ (γ : (NFlagQ V d.e).prod (GQ W)) (y : Orb W x₀) (p : flagN d × GA D W),
      Th ((γ : flagN d × GA D W) * p).1.1 * G ((γ : flagN d × GA D W) * p).2 *
        term ψ d W vS (om (((γ : flagN d × GA D W) * p).1.1, ((γ : flagN d × GA D W) * p).2) Φ) (γ • y).1 =
      Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
    intro γ y p
    have hmem := Subgroup.mem_prod.1 γ.2
    have hq1 : ((γ.1.1 : flagN d) : GA D V) ∈ GQ V := hmem.1
    have hq2 : γ.1.2 ∈ GQ W := hmem.2
    obtain ⟨M, hM⟩ := mt_mem_GQ_rat W hq2
    have hΨ := hω.om_pres (p.1.1, p.2) Φ hΦ
    have hΨ' := hω.om_pres (1, γ.1.2) _ hΨ
    have key : term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) Φ) (γ • y).1 =
        term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
      have hsplit : ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) =
          (((γ.1.1 : GA D V), 1) * ((1 : GA D V), γ.1.2)) * (p.1.1, p.2) := by
        ext <;> simp
      rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have t2 := (_root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ').2.1
      have t3 := (_root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ).2.2.1
      have e1 : (rat (M * y.1) : Mx D W.rank ρ) = rat (γ • y).1 ⬝ blockX d (γ.1.1 : GA D V) := by
        rw [hrel γ y, hM, rat_mul]
      rw [t2 _ hq1 γ.1.1.2 (γ • y).1 (M * y.1) e1, t3 _ hq2 (M * y.1) y.1 (by rw [hM, rat_mul])]
    have hT : Th ((γ.1.1 : GA D V) * p.1.1) = Th p.1.1 := hTh.left _ hq1 γ.1.1.2 _ p.1.2
    have hGG : G (γ.1.2 * p.2) = G p.2 := hG.1 _ hq2 p.2
    show Th ((γ.1.1 : GA D V) * p.1.1) * G (γ.1.2 * p.2) *
        term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) Φ) (γ • y).1 = _
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hT hGG) key
  obtain ⟨hl, hi⟩ := _root_.GlobalTheory.Unf.lintegral_integral_unfold_transitive (flagN d × GA D W) (vN.ν.prod vW.μ) ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) y₀ htrans
    (vN.𝓝 ×ˢ vW.𝓕) (𝓐 ×ˢ 𝓑) hF hG'
    (fun y p => Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1) hmeas hinv
  obtain ⟨hfin, hLA⟩ := _root_.GlobalTheory.Unf.mean_lift_eq_orbit_integral D hD ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ Th hx hTh G Φ hG hΦ
  simp only [hy₀] at hl hi
  have hfin' := hl ▸ hfin
  obtain ⟨hint, hLC⟩ := _root_.GlobalTheory.Unf.integral_base_term_coords D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hTh G Φ hG hΦ 𝓐 𝓑
    h𝓐.nullMeasurableSet h𝓑.nullMeasurableSet hlay hfin'
  exact ⟨hint, by rw [hLA, ← hi hfin, hLC]⟩

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedFunctionEqBesselPeriodIntegrand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.BesselIntegrand

theorem handFB_smul_om {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (c : ℂ) (h₁ : GA D B.A) :
    handFB s vL Y (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) 1 = c * handFB s vL Y Ξ h₁ := by
  unfold handFB
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (1, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
      one_mul]
  unfold pairKer
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem unfF_eq_besFun : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Φ → ∀ (h : GA D B.V) (h₁ : GA D B.A) (n : flagN B.d), unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) = besFun ψ 1 B.d B.o B.ζ (handFB s vL Y (flatFB s (s.om (1, h) Φ))) (rTrans h G) h₁ n := by
  intro D hD ψ σ J B s vL Y G Φ hΦ h h₁ n
  have h1 : IsThetaFunO ψ J.W B.V (s.om (1, h) Φ) := s.weil.om_pres _ _ hΦ
  have h2 : IsThetaFunO ψ J.W B.V (s.om (1, embA B.d B.o h₁) (s.om (1, h) Φ)) := s.weil.om_pres _ _ h1
  have e : s.om (1, n.1 * embA B.d B.o h₁ * h) Φ = s.om (1, n.1) (s.om (1, embA B.d B.o h₁) (s.om (1, h) Φ)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      one_mul, one_mul]
  have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B s _ h1 1 h₁
  rw [map_one] at c
  unfold unfF besFun rTrans
  rw [e, _root_.GlobalTheory.Unf.FB.UnipAct.flatFB_flagN D hD ψ σ J B s _ h2 n.1 n.2, c, handFB_smul_om]
  ring

end GlobalTheory.Unf.FB.BesselIntegrand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.UnrAll

theorem unrCorr_all : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun _ => True) := by
  intro _hDec hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw _
  by_cases hc : Formalism.IndefR.Lev.IsConjPl w w
  · exact GlobalTheory.DownInert.unrCorr_inert hHowe D G Pl0 T A Ks R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
  · exact GlobalTheory.SplitCorr.unrCorr_split D G Pl0 T A Ks R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw hc

end GlobalTheory.UnrAll
end

