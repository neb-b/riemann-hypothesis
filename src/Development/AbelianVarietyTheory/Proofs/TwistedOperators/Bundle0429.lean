module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0416
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneSimultaneousRightTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
noncomputable section

namespace GlobalTheory.BplusShift

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem embTop_mul (a b : GA D (G.V (.top 0))) : embTop G (a * b) = embTop G a * embTop G b := by
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  rw [e, e, e, map_mul]

theorem inner_left (W : G.Weil) (M : Vol G) (hM : M.IsRow) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)}
    (hφ : φ ∈ contLeft (G.V (.top 0))) (hF : F ∈ contLeft (G.V (.grid D.R.m 0))) {γ : GA D (G.V (.top 0))}
    (hγ : γ ∈ GQ (G.V (.top 0))) (h : GA D (G.V (.top 0))) :
    ∫ n in M.fdN, besInt W φ F (γ * h) n ∂M.νN = ∫ n in M.fdN, besInt W φ F h n ∂M.νN := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  have r1 := (hs γ (s γ)).2 rfl
  have r2 := (hs γ⁻¹ (s γ)⁻¹).2 (map_inv s _).symm
  have hδ : s γ ∈ GQ (G.V (.grid D.R.m 0)) := hq _ hγ
  let c : NFlag (G.V (.grid D.R.m 0)) G.besTop.e ≃ₜ* NFlag (G.V (.grid D.R.m 0)) G.besTop.e :=
    { toFun := fun n => ⟨s γ * n * (s γ)⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).1⟩
      invFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r2 n n.2).1⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e ↔ n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e := fun n => by
    change s γ * n.1 * (s γ)⁻¹ ∈ GQ (G.V (.grid D.R.m 0)) ↔ n.1 ∈ GQ (G.V (.grid D.R.m 0))
    rw [Subgroup.mul_mem_cancel_right _ (inv_mem hδ), Subgroup.mul_mem_cancel_left _ hδ]
  have hl : ∀ γ' ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      besInt W φ F (γ * h) (γ' * n) = besInt W φ F (γ * h) n := fun γ' hγ' n => by
    have hq' := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besInt, Subgroup.coe_mul]
    rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ'.2 n.2, GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ'.2 hq',
      one_mul, mul_assoc γ'.1, hF.2 _ hq']
  refine (GlobalTheory.Mem.TrueRecord.integral_aut _ hM.unip.1 hM.unip.2.1 hM.unip.2.2 c hc _ hl).symm.trans ?_
  congr 1
  funext n
  change φ (γ * h) * F ((s γ * n * (s γ)⁻¹) * embTop G (γ * h)) * star (besChar W.ψ G.besTop (s γ * n * (s γ)⁻¹)) =
    φ h * F (n * embTop G h) * star (besChar W.ψ G.besTop n)
  rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).2, hφ.2 γ hγ h, e, e, map_mul,
    show s γ * n * (s γ)⁻¹ * (s γ * s h) = s γ * (n * s h) by group, hF.2 _ hδ]

end GlobalTheory.BplusShift


open GlobalTheory.BplusShift in
theorem GlobalTheory.BplusShift.bplus_rTr : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ a : GA D (G.V (.top 0)),
      Bplus W M (rTr _ a φ) (rTr _ (embTop G a) F) = Bplus W M φ F := by
  intro D T L sc G W M hM φ hφ F hF a
  have hshift : ∀ h n, besInt W (rTr _ a φ) (rTr _ (embTop G a) F) h n = besInt W φ F (h * a) n := fun h n => by
    simp only [besInt, rTr]
    rw [embTop_mul, mul_assoc (n : GA D (G.V (.grid D.R.m 0)))]
  simp only [Bplus, hshift]
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  haveI := hμ
  haveI : (M.ν (.top 0)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hμ
  have hmp : MeasurePreserving (· * a) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a
  have hmp' : MeasurePreserving (· * a⁻¹) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a⁻¹
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a)
    (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)), Set.image_mul_right]
  have hF' : IsFundamentalDomain (GQ (G.V (.top 0))) ((· * a⁻¹) ⁻¹' M.fd (.top 0)) (M.ν (.top 0)) :=
    h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (h𝓕.setIntegral_eq hF' fun γ x => inner_left W M hM hφ hF γ.2 x).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruencesReductionMemSymmetricUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjGroup

theorem congr_red_mem_unipSym : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool), IsFrame β (II D).L → LocAt g e0 f0 z0 bw bwd ew β PP w → ∀ (x : (II D).Gf) (M : GL (Fin (Yc D 0).rank) (EAf D)), x ∈ (II D).Kset → (II D).fmat x = M.val → M ∈ St β → K2cong (II D) g e0 z0 bw x → upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k := by
  intro D g e0 f0 z0 bw bwd ew hF β PP w hβ hL x M hx hM hSt hc
  have hred := GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser β (II D).L hβ PP
  have hLf : ∀ v, v ∈ (II D).Lf → v ∈ Formalism.L2.Herm.hatL (F := ↥D.host.F) (E := D.host.E) (II D).L := by
    intro v hv
    have e := Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (II D).L
    exact (Set.ext_iff.mp e v).mp hv
  have hint : ∀ i : Fin D.R.k, ew ∈ IntAf (II D).F (II D).E ∧ sigA (II D) ew ∈ IntAf (II D).F (II D).E := by
    intro i
    obtain ⟨t, ht, he⟩ := hF.dual i i
    obtain ⟨t', ht', he'⟩ := Formalism.L2.SG.Pf.BunEx.Unip.Zsym (hF.dual i i)
    simp only [if_pos (Eq.refl i), ↓reduceIte] at he he'
    have h1 := Formalism.L2.SG.Pf.unitaryCongruence.hA_int (II D) (hF.mem.2.2 i).2 (hF.mem.2.2 i).1
    have h2 := Formalism.L2.SG.Pf.unitaryCongruence.hA_int (II D) (hF.mem.2.2 i).1 (hF.mem.2.2 i).2
    have hg : ((g : (II D).E ⊗[(II D).F] Af (II D).F)) ∈ IntAf (II D).F (II D).E := natCast_mem _ g
    constructor
    · have e1 : ew = hA (II D) (bwd i) (bw i) - (g : (II D).E ⊗[(II D).F] Af (II D).F) * t := by
        rw [← he]; exact (sub_sub_cancel _ _).symm
      rw [e1]; exact sub_mem h1 (mul_mem hg ht)
    · have e1 : sigA (II D) ew = hA (II D) (bw i) (bwd i) - (g : (II D).E ⊗[(II D).F] Af (II D).F) * t' := by
        rw [← he']; exact (sub_sub_cancel _ _).symm
      rw [e1]; exact sub_mem h2 (mul_mem hg ht')
  cases w
  ·
    have hR : RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (fun i => bwd (Fin.rev i)) z0) := hL.2.2.2
    refine GlobalTheory.T.reduction_mem_unipSym_of_flag_congruences g e0 f0 z0 (fun i => bwd (Fin.rev i)) bw β PP hβ hL.1 hR ?_ M hSt ?_ ?_ ?_ ?_
    · intro i
      refine ⟨(hF.mem.2.2 i).1, ?_⟩
      have hi : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (hint i).1
      have hs := hred.2.1 ⟨ew, hi⟩ (bw i) (hLf _ (hF.mem.2.2 i).1)
      have h0 := hL.2.1 hi
      simp only [Bool.false_eq_true, if_false] at h0
      rw [h0, zero_smul] at hs
      rw [hF.bw_w i]; exact hs
    · intro a; rw [← hM]; exact hc.1 a
    · rw [← hM]; exact hc.2.1
    · intro i
      rw [← hM]
      have hb := _root_.GlobalTheory.SeeConjBwd.bwd_move (II D) g e0 f0 z0 bw bwd ew hF x hx hc (Fin.rev i)
      have hsub : Set.range e0 ∪ bwd '' {l | Fin.rev i < l} ⊆
          Set.range e0 ∪ Set.range bw ∪ (fun j => bwd (Fin.rev j)) '' {j | j.1 < i.1} := by
        rintro v (hv | ⟨l, hl, rfl⟩)
        · exact Or.inl (Or.inl hv)
        · refine Or.inr ⟨Fin.rev l, ?_, by simp⟩
          have hl' : (Fin.rev i).1 < l.1 := hl
          simp only [Fin.val_rev] at hl'
          show (Fin.rev l).1 < i.1
          simp only [Fin.val_rev]; omega
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub hb
    · intro b
      rw [← hM]
      have hf := Formalism.L2.SG.Pf.BunEx.Unip.F1 hF hx hc b
      have hsub : Set.range e0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ∪ f0 '' {c | b < c} ⊆
          Set.range e0 ∪ {z0} ∪ Set.range (fun j => bwd (Fin.rev j)) ∪ Set.range bw ∪ f0 '' {c | b < c} := by
        rintro v ((((hv | hv) | hv) | hv) | hv)
        · exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hv)))
        · exact Or.inl (Or.inr hv)
        · obtain ⟨j, rfl⟩ := hv
          exact Or.inl (Or.inl (Or.inr ⟨Fin.rev j, by simp⟩))
        · exact Or.inr hv
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub hf
  ·
    have hR : RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bw z0) := hL.2.2.2
    refine GlobalTheory.T.reduction_mem_unipSym_of_flag_congruences g e0 f0 z0 bw bwd β PP hβ hL.1 hR ?_ M hSt ?_ ?_ ?_ ?_
    · intro i
      refine ⟨(hF.mem.2.2 i).2, ?_⟩
      have hi : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (hint i).2
      have hs := hred.2.1 ⟨sigA (II D) ew, hi⟩ (bwd i) (hLf _ (hF.mem.2.2 i).2)
      have h0 := hL.2.2.1 hi
      simp only [if_true] at h0
      rw [h0, zero_smul] at hs
      rw [hF.bwd_w i]; exact hs
    · intro a; rw [← hM]; exact hc.1 a
    · rw [← hM]; exact hc.2.1
    · intro i
      rw [← hM]
      have hsub : Set.range e0 ∪ bw '' {j | j.1 < i.1} ⊆ Set.range e0 ∪ Set.range bwd ∪ bw '' {j | j.1 < i.1} :=
        Set.union_subset_union_left _ Set.subset_union_left
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub (hc.2.2 i)
    · intro b
      rw [← hM]
      exact Formalism.L2.SG.Pf.BunEx.Unip.F1 hF hx hc b

end GlobalTheory.SeeConjGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRange
section
open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowFun

theorem coeff_mem_of_mul_eq {s : Type} (K' : Subfield ℂ) (f P Q : MvPolynomial s ℂ) (hP : P ≠ 0)
    (hPK : ∀ m, AddMonoidAlgebra.coeff P m ∈ K') (hQ : ∀ m, AddMonoidAlgebra.coeff Q m ∈ K') (h : f * P = Q) :
    ∀ m, AddMonoidAlgebra.coeff f m ∈ K' := by
  classical
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.RowRat.exists_proj K'
  let g : MvPolynomial s ℂ := ∑ m ∈ f.support, monomial m (φ (AddMonoidAlgebra.coeff f m))
  have hg : ∀ m, AddMonoidAlgebra.coeff g m = φ (AddMonoidAlgebra.coeff f m) := by
    intro m
    simp only [g, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [notMem_support_iff.mp hm, map_zero]
  have key : g * P = f * P := by
    ext m
    have hfix : AddMonoidAlgebra.coeff (f * P) m = φ (AddMonoidAlgebra.coeff (f * P) m) := by
      rw [h]; exact (hφ1 ⟨_, hQ m⟩).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfix, coeff_mul, coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hg]
    have hs := φ.map_smul (⟨AddMonoidAlgebra.coeff P x.2, hPK _⟩ : K') (AddMonoidAlgebra.coeff f x.1)
    rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul] at hs
    rw [mul_comm, ← hs, mul_comm]
  have hgf : g = f := mul_right_cancel₀ hP key
  intro m
  rw [← hgf, hg]
  exact hφ2 _

theorem coeff_funOf_mem_range {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type}
    [Field L] (κ : L →+* ℂ) (hR : GlobalTheory.FunObj.ReadOK σ) (F : VV ℂ σ)
    (hF : ∀ m, AddMonoidAlgebra.coeff F.1 m ∈ Set.range κ) :
    ∀ m, AddMonoidAlgebra.coeff (GlobalTheory.FunObj.funOf σ F).1 m ∈ Set.range κ := by
  classical
  have hf := hR.1 F
  unfold GlobalTheory.FunObj.IsFunForm at hf
  let G : MvPolynomial (ι × Fin n × Fin n) L :=
    ∑ m ∈ (F.1 : MvPolynomial (ι × Fin n × Fin n) ℂ).support,
      monomial m (Function.invFun κ (AddMonoidAlgebra.coeff F.1 m))
  have hG : MvPolynomial.map κ G = F.1 := by
    ext m
    rw [coeff_map]
    simp only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · exact Function.invFun_eq (hF m)
    · simp [notMem_support_iff.mp hm]
  have hmem : ∀ (p : MvPolynomial (ι × Fin n × Fin n) L) m,
      AddMonoidAlgebra.coeff (MvPolynomial.map κ p) m ∈ κ.fieldRange := fun p m => by
    rw [coeff_map]; exact RingHom.mem_fieldRange_self κ _
  have hmem_eq₁ : MvPolynomial.map κ (∏ τ, Formalism.L2.Ker.frDet L n τ ^ ∑ a, (σ τ).natW a)
      = ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ ∑ a, (σ τ).natW a := by
    simp only [map_prod, map_pow, GlobalTheory.BrRat.map_frDet]
  have hmem_eq₂ : MvPolynomial.map κ (GlobalTheory.FunObj.dualSubst L ι n G *
      ∏ τ, Formalism.L2.Ker.frDet L n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat)
      = GlobalTheory.FunObj.dualSubst ℂ ι n F.1 *
      ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat := by
    simp only [map_mul, map_prod, map_pow, GlobalTheory.BrRat.map_frDet, GlobalTheory.BrRat.map_dualSubst, hG]
  intro m
  have := coeff_mem_of_mul_eq κ.fieldRange _ _ _
    (Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (GlobalTheory.FunObj.funFrDet_ne_zero τ))
    (fun m => by
      rw [← hmem_eq₁]; exact hmem _ m)
    (fun m => by
      rw [← hmem_eq₂]; exact hmem _ m) hf m
  exact RingHom.mem_fieldRange.mp this

end GlobalTheory.RowFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.EmbAtPlace

variable {D : D7}

theorem mat_ext {m n : Type*} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {M N : Matrix m n (Formalism.L2.Theta.AE D)}
    (h1 : M.map (Formalism.L2.Theta.finPart D) = N.map (Formalism.L2.Theta.finPart D))
    (h2 : ∀ τ, M.map (fun z => θ τ (Formalism.L2.Theta.infPart D z)) = N.map (fun z => θ τ (Formalism.L2.Theta.infPart D z))) :
    M = N := by
  ext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun (h2 τ) i) j

theorem vec_ext {n : Type*} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {v w : n → Formalism.L2.Theta.AE D}
    (h1 : ∀ i, Formalism.L2.Theta.finPart D (v i) = Formalism.L2.Theta.finPart D (w i))
    (h2 : ∀ τ i, θ τ (Formalism.L2.Theta.infPart D (v i)) = θ τ (Formalism.L2.Theta.infPart D (w i))) : v = w := by
  funext i
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, sub_eq_zero]; exact h1 i
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact h2 τ i

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (Formalism.L2.Theta.infPart D (incA D e)) = tauE D τ e := by
  have : Formalism.L2.Theta.infPart D (incA D e) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] e := by
    simp [Formalism.L2.Theta.infPart, incA, inclR]
  rw [this]; exact (hθ τ).1 e

end GlobalTheory.EmbAtPlace

namespace GlobalTheory.EmbAtPlace

theorem embRel_atTau : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (τ : D.what₂.Tau)
    (h : Matrix (Fin A.rank) (Fin A.rank) ℂ) (g : Matrix (Fin B.rank) (Fin B.rank) ℂ), h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ) →
    g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ) → GlobalTheory.RealBessel.IsEmb (gramAt D B τ) ((frameMat B A ι).map (tauE D τ)) g h →
    EmbRel B A ι (atTau θ B τ g) (atTau θ A τ h) := by
  classical
  intro D θ hθ A B ι τ h g hh hg hE
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hX := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hg
  have hY := GlobalTheory.PointAtPlaceHom.atTau_spec hθ A τ hh
  have fX : (matHom B (atTau θ B τ g)).1.map (Formalism.L2.Theta.finPart D) = 1 :=
    (congrArg (fun k : GL (Fin B.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => k.val) (MonoidHom.mem_ker.1 hX.1)).trans Units.val_one
  have fY : (matHom A (atTau θ A τ h)).1.map (Formalism.L2.Theta.finPart D) = 1 :=
    (congrArg (fun k : GL (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => k.val) (MonoidHom.mem_ker.1 hY.1)).trans Units.val_one
  have iX : ∀ τ', (matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      if τ' = τ then g else 1 := fun τ' => by
    split_ifs with e
    · subst e; exact hX.2.1
    · exact hX.2.2 τ' e
  have iY : ∀ τ', (matHom A (atTau θ A τ h)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      if τ' = τ then h else 1 := fun τ' => by
    split_ifs with e
    · subst e; exact hY.2.1
    · exact hY.2.2 τ' e
  have iF : ∀ τ', ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      (frameMat B A ι).map (tauE D τ') := fun τ' => by
    rw [Matrix.map_map]; congr 1; funext e; exact GlobalTheory.EmbAtPlace.theta_incA hθ τ' e
  refine ⟨?_, fun x hx => ?_⟩
  · refine GlobalTheory.EmbAtPlace.mat_ext hσ ?_ fun τ' => ?_
    · rw [Matrix.map_mul, Matrix.map_mul, fX, fY, Matrix.one_mul, Matrix.mul_one]
    · let φ : Formalism.L2.Theta.AE D →+* ℂ := (θ τ').comp (Formalism.L2.Theta.infPart D)
      change Matrix.map (_ * _) ⇑φ = Matrix.map (_ * _) ⇑φ
      rw [Matrix.map_mul, Matrix.map_mul]
      change (matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *
          ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
        ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *
          (matHom A (atTau θ A τ h)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z))
      rw [iX, iY, iF]
      split_ifs with e
      · subst e; exact hE.1
      · rw [Matrix.one_mul, Matrix.mul_one]
  · refine GlobalTheory.EmbAtPlace.vec_ext hσ (fun i => ?_) fun τ' i => ?_
    · rw [RingHom.map_mulVec, fX, Matrix.one_mulVec]; rfl
    · let φ : Formalism.L2.Theta.AE D →+* ℂ := (θ τ').comp (Formalism.L2.Theta.infPart D)
      change φ _ = φ _
      rw [RingHom.map_mulVec]
      change ((matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *ᵥ
        fun j => θ τ' (Formalism.L2.Theta.infPart D (incA D (x j)))) i = θ τ' (Formalism.L2.Theta.infPart D (incA D (x i)))
      simp only [GlobalTheory.EmbAtPlace.theta_incA hθ]
      rw [iX]
      split_ifs with e
      · subst e
        have h0 : (((frameMat B A ι).map (tauE D τ'))ᴴ * gramAt D B τ') *ᵥ (fun j => tauE D τ' (x j)) = 0 := by
          have hm : ((frameMat B A ι).map (tauE D τ'))ᴴ * gramAt D B τ' =
              (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram).map (tauE D τ') := by
            rw [Matrix.map_mul]
            congr 1
            ext a b
            simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
            exact (Formalism.IndefR.Eqv.tauE_star D τ' _).symm
          rw [hm]
          funext i
          have := RingHom.map_mulVec (tauE D τ') (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram) x i
          simp only [Function.comp_def] at this
          rw [← this, hx]
          simp
        exact congrFun (hE.2 _ h0) i
      · rw [Matrix.one_mulVec]

end GlobalTheory.EmbAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThetaSeparates

theorem eq_zero_of_thetaSum_rho : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
    (∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = 0) → Φ = 0 := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Φ hΦ h
  classical
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  obtain ⟨𝓕₁, hF, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain F (Fin n × Fin d) μ inferInstance
  funext x
  have hP := GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq F ψ (GlobalTheory.StdCharFromIsStd.isCharAF hψ)
    (Fin n × Fin d) μ inferInstance 𝓕₁ hF htop Φ hΦ x
  have hz : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = 0 := by
    intro y
    have := h (M.co.e.symm (x, y))
    simpa [GlobalTheory.WeilM.Darboux.rho] using this
  simp only [hz, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, MeasureTheory.lintegral_zero] at hP
  have hs := (mul_eq_zero.mp hP.symm).resolve_left h0
  have h1 := ENNReal.tsum_eq_zero.mp hs 0
  have e : ((fun _ => (0 : AF F)) : Fin n × Fin d → AF F) + x = x := zero_add x
  simp only [map_zero, enorm_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h1
  simpa [e] using h1

end GlobalTheory.ThetaSeparates
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerMovedVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem toPair_mul (p : Pair T) (g g' : GA D (G.V p.small)) (h h' : GA D (G.V p.big)) :
    G.toPair p (g * g') (h * h') = G.toPair p g h * G.toPair p g' h' := by
  cases p <;> simp [GridData.toPair, map_mul, Prod.ext_iff]

end GlobalTheory.RowClaim
end
end

