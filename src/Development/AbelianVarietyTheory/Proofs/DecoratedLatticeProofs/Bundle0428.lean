module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralGlueLocalHomotheties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatGlue

variable {D : D7}

theorem mt_mul (S : HSp D) (a b : GA D S) : Formalism.L2.Theta.mt S (a * b) = Formalism.L2.Theta.mt S a * Formalism.L2.Theta.mt S b := by
  first | rfl | simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := by
  first | rfl | simp [Formalism.L2.Theta.mt]

theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ GlobalTheory.FinPl.congGrp V I ↔ ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold GlobalTheory.FinPl.congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem idAt_le_idOff {v w : GlobalTheory.FinPl.Pl D} (h : v ≠ w) : idAt D (· = w) ≤ GlobalTheory.FinPl.idOff D (· = v) := by
  intro a ha
  unfold idAt at ha
  unfold GlobalTheory.FinPl.idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = v := u.2
  exact ha.2 ⟨u.1, fun e => h (hu.symm.trans e)⟩

theorem mulVec_fix {S : HSp D} {v w : GlobalTheory.FinPl.Pl D} (hvw : v ≠ w) {h : GA D S} (hh : h ∈ grpAt S (· = w))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) : Formalism.L2.Theta.mt S h *ᵥ y = y := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (_root_.GlobalTheory.FinPl.localComponents D (· = v)).1
  have hh' := (mem_congGrp).1 hh
  have key : (Formalism.L2.Theta.mt S h - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ (hy j)
    have h2 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ GlobalTheory.FinPl.idOff D (· = v) :=
      Ideal.mul_mem_right _ _ (idAt_le_idOff hvw (by simpa using hh' i j))
    rw [← (hA _).1 h1]
    exact (hO _).1 h2
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem scal_mulVec {n : ℕ} (c : AE D) (y : Fin n → AE D) : (c • (1 : Matrix (Fin n) (Fin n) (AE D))) *ᵥ y = c • y := by
  first | rw [Matrix.smul_mulVec, Matrix.one_mulVec] | simp [Matrix.smul_mulVec] | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])

end GlobalTheory.Core.Mi.LatGlue

namespace GlobalTheory.Core.Mi.LatGlue

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem glue_finset {V A : HSp D} (e : GA D A →* GA D V)
    (he : ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v))
    (a : GlobalTheory.FinPl.Pl D → GA D A) (c : GlobalTheory.FinPl.Pl D → AE D) (z : GlobalTheory.FinPl.Pl D → GA D V)
    (ha : ∀ v, CenAt A v (a v)) (hz : ∀ v, CenAt V v (z v))
    (hzm : ∀ v, Formalism.L2.Theta.mt V (z v) = c v • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) (s : Finset (GlobalTheory.FinPl.Pl D)) :
    ∃ α ∈ GfC A, α ∈ Subgroup.center (GA D A) ∧ ∃ ζ ∈ Subgroup.center (GA D V),
      (∀ v ∈ s, ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
        Formalism.L2.Theta.mt V (e α) *ᵥ y = Formalism.L2.Theta.mt V (e (a v)) *ᵥ y ∧ Formalism.L2.Theta.mt V ζ *ᵥ y = c v • y) ∧
      (∀ v ∉ s, ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
        Formalism.L2.Theta.mt V (e α) *ᵥ y = y ∧ Formalism.L2.Theta.mt V ζ *ᵥ y = y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_mem _, one_mem _, 1, one_mem _, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ y _ => ?_⟩
    rw [map_one, mt_one, Matrix.one_mulVec]
    exact ⟨rfl, rfl⟩
  | insert w s hws ih =>
    obtain ⟨α, hαG, hαC, ζ, hζC, hin, hout⟩ := ih
    have hwG : a w ∈ GfC A := ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff A _ (a w)).1 (ha w).1).1
    refine ⟨a w * α, mul_mem hwG hαG, mul_mem (ha w).2 hαC, z w * ζ, mul_mem (hz w).2 hζC, ?_, ?_⟩
    · intro v hv y hy
      rcases Finset.mem_insert.1 hv with rfl | hvs
      · obtain ⟨h1, h2⟩ := hout v hws y hy
        refine ⟨?_, ?_⟩
        · rw [map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1]
        · rw [mt_mul, ← Matrix.mulVec_mulVec, h2, hzm, scal_mulVec]
      · have hvw : v ≠ w := fun h => hws (h ▸ hvs)
        obtain ⟨h1, h2⟩ := hin v hvs y hy
        have ca : a w * α = α * a w := ((Subgroup.mem_center_iff.1 (ha w).2) α).symm
        have cz : z w * ζ = ζ * z w := ((Subgroup.mem_center_iff.1 (hz w).2) ζ).symm
        refine ⟨?_, ?_⟩
        · rw [ca, map_mul, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (he w _ (ha w).1) hy, h1]
        · rw [cz, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (hz w).1 hy, h2]
    · intro v hv y hy
      have hvw : v ≠ w := fun h => hv (h ▸ Finset.mem_insert_self w s)
      have hvs : v ∉ s := fun h => hv (Finset.mem_insert_of_mem h)
      obtain ⟨h1, h2⟩ := hout v hvs y hy
      refine ⟨?_, ?_⟩
      · rw [map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1, mulVec_fix hvw (he w _ (ha w).1) hy]
      · rw [mt_mul, ← Matrix.mulVec_mulVec, h2, mulVec_fix hvw (hz w).1 hy]


set_option maxHeartbeats 800000 in
theorem glue : ∀ (D : D7) (V A : HSp D) (e : GA D A →* GA D V) (g : GA D V) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → (∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v)) → (∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves V c (g * e a) L M v) → ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ z ∈ Subgroup.center (GA D V), Moves V (z * (g * e a)) L M (fun _ => True) := by
  intro D V A e g L M hL hM he hloc
  classical
  choose a c ha hc hs using hloc
  choose z hz hzm using fun v => _root_.GlobalTheory.Core.Mi.LatMatch.exists_cenAt_scalar D V v (c v) (hc v)
  obtain ⟨M', hM'sd, hgM'⟩ := (_root_.GlobalTheory.FinPl.GlobImage.glob D V L hL).1 g
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have hcompare := by
    first
    | exact GlobalTheory.FinPl.latV_eq_off_finite D V M' M (hfull V M' hM'sd) (hfull V M hM)
    | exact GlobalTheory.FinPl.latV_eq_off_finite D V M' M (hfull V M' hM'sd) hM.1
  obtain ⟨T, hT⟩ := hcompare
  have hoff : ∀ v ∉ T, Moves V g L M (· = v) := fun v hv y hy => by
    rw [hgM' _ y hy, hT v hv]
  obtain ⟨α, hαG, hαC, ζ, hζC, hin, hout⟩ := glue_finset e he a c z ha hz hzm T
  refine ⟨α, hαG, hαC, ζ, hζC, ?_⟩
  have comm : ζ * (g * e α) = g * e α * ζ := ((Subgroup.mem_center_iff.1 hζC) _).symm
  have hmt : ∀ y : Fin V.rank → AE D, Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y =
      Formalism.L2.Theta.mt V g *ᵥ (Formalism.L2.Theta.mt V (e α) *ᵥ (Formalism.L2.Theta.mt V ζ *ᵥ y)) := fun y => by
    rw [comm, mt_mul, mt_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have loc : ∀ v, Moves V (ζ * (g * e α)) L M (· = v) := by
    intro v y hy
    rw [hmt]
    by_cases hv : v ∈ T
    · obtain ⟨h1, h2⟩ := hin v hv y hy
      rw [h2, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mt_mul]
      exact hs v y hy
    · obtain ⟨h1, h2⟩ := hout v hv y hy
      rw [h2, h1]
      exact hoff v hv y hy
  intro y hy
  rw [GlobalTheory.FinPlLoc.part_lat _ V L y hL.1, GlobalTheory.FinPlLoc.part_lat _ V M _ hM.1]
  have hsupp : ∀ i, (Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y) i ∈ idAt D (fun _ => True) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  refine and_congr (iff_of_true hy hsupp) (forall_congr' fun v => imp_congr_right fun _ =>
    forall_congr' fun x => forall_congr' fun hx => ?_)
  have hxy : ∀ i, (x • y) i ∈ idAt D (· = v) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hx.1
  rw [← Matrix.mulVec_smul]
  exact loc v (x • y) hxy

end GlobalTheory.Core.Mi.LatGlue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsKerTie
section
section BaseLevels₂

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Core.DefKer.stdRd_keep {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hS : I.StdKer l Z t) :
    ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ t'.O = t.O ∧ t'.ent = t.ent := by
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, rfl, rfl⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a


end BaseLevels₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Core GlobalTheory.Core.Cls NumberField IsDedekindDomain GlobalTheory.Mem.Db Formalism.L2 Formalism.L2.Ker Formalism.L2.Forms

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThetaLiftSpacesPositiveIndexWithLineNorms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.SeeSaw.YRat

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj _ _ _

theorem posDef_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

theorem defSpace {D : D7} (hX : ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) {j : ℕ} (hj : j ≤ D.R.m) :
    (D.sp.X j).SigOK ∧ (∀ τ, (D.sp.X j).sig τ = (D.R.N j, 0)) ∧ CoCpt (D.sp.X j) := by
  have hs : (D.sp.X j).SigOK := D.sp.X_sig j
  have hr : (D.sp.X j).rank = D.R.N j := D.sp.X_rank j hj
  refine ⟨hs, fun τ => by rw [hX j hj τ, hr], ?_⟩
  refine (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D (D.sp.X j)).2 fun τ => ?_
  have h1 := hs (tauE D τ)
  rw [hX j hj (tauE D τ)] at h1
  exact posDef_of_sig _ h1

theorem spaces_of_index : ∀ (D : D7) (u : D.what₂.Word), (∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) → (∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (b : BesAt V (D.sp.X j) ρ), V.rank = D.R.rankY j ∧ V.SigOK ∧ (∀ τ, V.sig τ = sigYD D.R j) ∧ (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E)) ∧ ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (_ : JacAt V (D.sp.X (j + 1)) ρ), V.rank = D.R.rankY (j + 1) ∧ V.SigOK ∧ ∀ τ, V.sig τ = sigYD D.R (j + 1) := by
  intro D u hX
  have hsum := _root_.GlobalTheory.OrthSumSp.exists_orthSum_hypSum D
  have hvol := GlobalTheory.Unf.VolExist.measures_exist D
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  obtain ⟨π, -, hπ, -⟩ := D.T_norm u
  have hππ : (π : D.host.E) * star (π : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [star_eq_conj]; exact hπ
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
    have := (D.mem u).A.T_prime.ne_zero
    exact_mod_cast this
  have hπ0 : (π : D.host.E) ≠ 0 := by
    intro h0; apply hT0; rw [← hππ, h0, zero_mul]
  refine ⟨?_, ?_⟩
  · intro j ρ h
    obtain ⟨hXs, hXsig, hXc⟩ := defSpace hX (j := j) (by omega)
    have hXr : (D.sp.X j).rank = D.R.N j := D.sp.X_rank j (by omega)
    set c : D.host.E := (π : D.host.E) / D.host.xi0 ^ (j / 2) with hc
    have hc0 : c ≠ 0 := div_ne_zero hπ0 (pow_ne_zero _ hxi)
    obtain ⟨L, ζ, hline, hLs, hLn, hLsig⟩ := GlobalTheory.T.exists_hermitianLine_vector_prescribed_norm D c (-1) hc0
    obtain ⟨V₀, o, hV₀s, hV₀sig⟩ := hsum.1 (D.sp.X j) L hXs hLs
    obtain ⟨V, d, hVs, hVsig⟩ := hsum.2 V₀ ρ hV₀s
    refine ⟨V, ⟨V₀, L, d, o, ζ, hline, hXc, (hvol.2.1 _ _ _ d).some⟩, ?_, hVs, ?_, ?_⟩
    · have h1 := d.rank_add
      have h2 := o.rank_add
      have h3 : L.rank = 1 := hline.1
      have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
      simp only [Ranks.rankY, Ranks.r]
      rw [hXr] at h2
      simp only [Ranks.N] at h2
      omega
    · intro τ
      have hL : L.sig τ = (0, 1) := by rw [hLsig τ]; decide
      rw [hVsig τ, hV₀sig τ, hXsig τ, hL]
      have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
      simp only [sigYD, Ranks.rankY, Ranks.r, Ranks.N, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> omega
    · show (star ζ ⬝ᵥ L.gram *ᵥ ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = _
      rw [hLn, ← hππ, hc, star_div₀, star_pow]
      have hs0 : star D.host.xi0 ≠ 0 := star_ne_zero.2 hxi
      field_simp
      push_cast
      ring
  · intro j ρ h
    obtain ⟨hXs, hXsig, hXc⟩ := defSpace hX (j := j + 1) (by omega)
    have hXr : (D.sp.X (j + 1)).rank = D.R.N (j + 1) := D.sp.X_rank (j + 1) (by omega)
    obtain ⟨V, d, hVs, hVsig⟩ := hsum.2 (D.sp.X (j + 1)) ρ hXs
    refine ⟨V, ⟨d, hXc, (hvol.2.1 _ _ _ d).some⟩, ?_, hVs, ?_⟩
    · have h1 := d.rank_add
      rw [hXr] at h1
      have h4 : (j + 1) * (D.R.t + 1) = (j + 1) * D.R.t + (j + 1) := by ring
      simp only [Ranks.N] at h1
      simp only [Ranks.rankY, Ranks.r]
      omega
    · intro τ
      rw [hVsig τ, hXsig τ]
      have h4 : (j + 1) * (D.R.t + 1) = (j + 1) * D.R.t + (j + 1) := by ring
      simp only [sigYD, Ranks.rankY, Ranks.r, Ranks.N, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> omega

end GlobalTheory.SeeSaw.YRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZero
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory

theorem coord_first_isotropic_ne_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : 1 ≤ D.R.rS), (fun i : Fin (D.sp.Y 0).rank => X.ιE (X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) i))) ≠ 0 := by
  intro D X h hr hzero
  have hrepr : X.bas.repr (X.eX ⟨0, hr⟩) = 0 := by
    ext j
    have := congrFun hzero (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h).symm j)
    simpa [Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd,
      Formalism.L2.SG.HidaSetting.crdOf] using this
  have hx : X.eX ⟨0, hr⟩ = 0 := by
    simpa using hrepr
  have hef := X.ef ⟨0, hr⟩ ⟨0, hr⟩
  rw [hx] at hef
  simp at hef

end GlobalTheory
end

