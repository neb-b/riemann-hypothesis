module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseMovesVectorZ
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0066
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0072
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0063
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0477
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0308
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptExStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptEx' : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.adaptEx_alt | exact _root_.GlobalTheory.BigOn.Exp.adaptEx_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.adaptEx_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdelicEmbeddingInverseVector
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.LocMod Matrix
noncomputable section
namespace GlobalTheory.MiTop.MoveZ
section Two
variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
end Two
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem addChar_uniformizer_eq_chi_of_gRead (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (PP : (_root_.GlobalTheory.Fam.pk_z W).Pg) : ∃ χ : 𝓞 D.host.E → ℂ, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ)
    (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ i, pl i = PP → ∀ z : 𝓞 D.host.E,
      ((G i).S.ψ ((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k) * (ofSplit (G i).q).pr (z : D.host.E)) : ℂ) = χ z := by
  classical
  have hr : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hk : 2 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  let a : Fin D.R.r := ⟨0, by omega⟩
  let b : Fin D.R.r := ⟨1, by omega⟩
  have hab : a ≠ b := fun e => by have := congrArg Fin.val e; simp [a, b] at this
  let g : 𝓞 D.host.E → ∀ P : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP P.1) := fun z P =>
    elem a b hab (Ideal.Quotient.mk P.1.asIdeal (if P = PP then z else 0))
  refine ⟨fun z => if h : g z ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H then (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g z, h⟩ : ℂˣ) : ℂ) else 0, ?_⟩
  intro u f v n G pl hG i hi z
  have hex : ∀ j, ∃ x, GlobalTheory.LevZero.Red (G j) (pl j).1 x (g z (pl j)) := fun j =>
    (GlobalTheory.LevZero.exists_red_iff_isPat (G j) (pl j).1 (hG.idem j).1 _).2
      (isPat_elem a b hab (Or.inl ⟨by simp only [a]; omega, by simp only [b]; omega, by simp [a, b]⟩) _)
  have hmem : g z ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hG.lev (g z)).1.2 hex
  choose x hx using hex
  have hchi := (hG.lev (g z)).2 hmem x hx
  have hlam : ∀ j, (((G j).S.P.lam (x j) : ℂˣ) : ℂ) = (G j).S.ψ ((((G j).S.ϖ⁻¹ : (G j).kˣ) : (G j).k) *
      (ofSplit (G j).q).pr ((if pl j = PP then z else 0 : 𝓞 D.host.E) : D.host.E)) := fun j =>
    GlobalTheory.LevZero.lam_eq_of_red (G j) (pl j).1 (hG.idem j).1 (x j) _ (hx j) _
      (edgeSum_elem a b hab ⟨rfl, by simp only [a]; omega⟩ _).symm
  simp only [dif_pos hmem]
  rw [hchi, Units.coe_prod, Finset.prod_eq_single i (fun j _ hj => ?_) (by simp), hlam, if_pos hi]
  rw [hlam, if_neg (fun e => hj (pl.injective (e.trans hi.symm)))]
  simp [Place.pr]
set_option maxHeartbeats 1000000 in
theorem base_inv_alt_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hG : _root_.GlobalTheory.Fam.LocalGroupReading f G pl)
    (hB : _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G) (i : Fin n) : ∃ j₀ : Fin (Yc D 0).rank, j₀.val = D.R.k + D.R.rS ∧ ∀ r,
      toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
          (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))) r =
      toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r j₀ := by
  have hs := (G i).hs
  have hodd := (G i).S.odd
  have hρ : D.R.rS = (G i).S.ρ := by unfold Ranks.rS; omega
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by omega
  have he := (hG.idem i).1
  obtain ⟨μ, lam, hμ, hv, hτ⟩ := hB.norm
  have hsc := sc_mul_mu (G i) μ lam hμ o.ζ₀ hτ (hB.last i)
  obtain ⟨e, hord, hM⟩ := hG.frame i 0 ((G i).s + 1) (Nat.zero_add _)
  let p : Fin ((G i).s + 1) := ⟨D.R.rS, by omega⟩
  refine ⟨e (.inl (.inr p)), hord _, fun r => ?_⟩
  refine e_mul_of_prF (G i).q he _ _ _ ?_
  refine map_inv_mulVec ((G i).q.prF he) _ _ (fun r => ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r (e (.inl (.inr p)))) _ (fun r => ?_) r
  choose lf hlf using fun x : Formalism.IndefR.Datum.EAf D => GlobalTheory.ResLoc.toEAf_surj x
  have h1 := congrFun (congrFun (hM (((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) (Matrix.ext fun a b => hlf _)) r) (e (.inl (.inr p)))
  have h2 : (G i).q.prF he (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0)).val *ᵥ
      fun r => ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r (e (.inl (.inr p)))) r) =
      (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) r (e (.inl (.inr p)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hlf (((_root_.GlobalTheory.Fam.pk_z W).βY 0).val a _)]
    exact (congrArg ((G i).q.prF he) ((toEAf D).map_mul _ _).symm).trans ((G i).q.prF_toEAf he _)
  have h3 : (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) r (e (.inl (.inr p)))) =
      ((G i).FY 0 ((G i).s + 1) (Nat.zero_add _)).β r (.inr p) * ((G i).S.ϖ : (G i).k) ^ (D.R.rS + 1) := by
    refine h1.trans ?_
    rw [submatrix_apply, Equiv.symm_apply_apply, GlobalTheory.LevZeroUp.bas_val, mul_diagonal]
    rw [GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin D.R.k) (Fin D.R.t) (l := (G i).s + 1) 0 ((G i).s + 1) (Nat.zero_add _) p]
    rfl
  have h4 := ((G i).bes 0 D.R.rS h₀ ((G i).s + 1) (Nat.zero_add _)).2.2.2.1 p rfl r
  have h5 : B.d.i₀ *ᵥ vecB B.o B.ζ = (f.c.B 0 D.R.rS h₀).d.i₀ *ᵥ vecB (f.c.B 0 D.R.rS h₀).o (f.c.B 0 D.R.rS h₀).ζ :=
    eq_of_heq (congr_arg_heq (fun B' : BesLev D D.R.rS => B'.d.i₀ *ᵥ vecB B'.o B'.ζ) (hB.lev h₀))
  rw [← h5, hv r] at h4
  have h6 : (G i).q.prF he (algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      (ofSplit (G i).q).pr (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) :=
    (G i).q.prF_toEAf he (incA D _)
  have h7 : ∀ x y, (ofSplit (G i).q).pr (x * y) = (ofSplit (G i).q).pr x * (ofSplit (G i).q).pr y := fun x y =>
    ((G i).q.pr.comp (incA D)).map_mul x y
  rw [h7, ← mul_assoc, hsc, one_mul] at h4
  rw [h6, h2, h3, h4, mul_comm, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
theorem inv_mulVec_adelic_embedding_eq_self (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    (g : GA D (D.sp.X 0)) :
    ((Formalism.IndefR.Lev.finE (D.sp.Y 0) (embA B.d B.o g))⁻¹).val *ᵥ (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) := by
  have h := GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hW.bot.idE (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.zR u)
    (Or.inr rfl) (embA B.d B.o g)⁻¹ ((B.tieH _).1 ((embA B.d B.o).range.inv_mem ⟨g, rfl⟩))
  funext r
  rw [← map_inv]
  exact ((toEAf D).map_mulVec _ _ r).symm.trans (congrArg (toEAf D) (congrFun h r))
end GlobalTheory.MiTop.MoveZ
open GlobalTheory.MiTop.MoveZ in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MiTop.base_moves_vector_z_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, ∃ Γ : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) = toEAf D ei • (θ • Γ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr PP hPP
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.MiTop.MoveZ.addChar_uniformizer_eq_chi_of_gRead W ⟨PP, hPP⟩
  by_cases hex : ∃ u, ∃ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B
  swap
  · exact ⟨0, fun u f B h => absurd ⟨u, f, B, h⟩ hex⟩
  obtain ⟨u₀, f₀, B₀, k₀, _, _, _, _, ι₀, v₀, o₀, n₀, G₀, pl₀, -, -, -, -, -, hG₀, hB₀⟩ := hex
  obtain ⟨i₀, hi₀⟩ := pl₀.surjective ⟨PP, hPP⟩
  have he₀ : Formalism.L2.NTheta.IsIdemAt (G₀ i₀).q.e PP := by have := (hG₀.idem i₀).1; rwa [hi₀] at this
  obtain ⟨j₀, hj₀, -⟩ := _root_.GlobalTheory.MiTop.MoveZ.base_inv_alt_alt W f₀ B₀ v₀ o₀ G₀ pl₀ hG₀ hB₀ i₀
  refine ⟨fun r => toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) *
    ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r j₀, ?_⟩
  rintro u f B ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, -, -, -, -, hG, hB⟩ a₀ a -
  obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
  have he : Formalism.L2.NTheta.IsIdemAt (G i).q.e PP := by have := (hG.idem i).1; rwa [hi] at this
  have hee : (G₀ i₀).q.e = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique he₀ he
  obtain ⟨j, hj, hz⟩ := _root_.GlobalTheory.MiTop.MoveZ.base_inv_alt_alt W f B v o G pl hG hB i
  obtain rfl : j = j₀ := Fin.ext (hj.trans hj₀.symm)
  have hrat := unif_ratio (G₀ i₀).q (G i).q he₀ hee (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (G₀ i₀).char (G i).char (G₀ i₀).S.cond _ _
    (G₀ i₀).S.unif (G i).S.unif fun z => (hχ u₀ f₀ v₀ n₀ G₀ pl₀ hG₀ i₀ hi₀ z).trans (hχ u f v n G pl hG i hi z).symm
  obtain ⟨θ, hθ, h1, h2⟩ := exists_theta (G₀ i₀).q he₀ _ (pow_sub_one_lt hrat (D.R.rS + 1))
  refine ⟨θ, hθ, h1, fun ei hei => ?_⟩
  obtain rfl : ei = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique hei he
  have h3 : toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) = toEAf D (G i).q.e * θ *
      toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) := by
    rw [← hee, h2, ← RingHom.map_mul, ← sec_mul_sec, ← mul_pow, mul_right_comm, Units.mul_inv, one_mul, ← map_pow, sec_chg]
  have h4 : (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) *
      (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      ((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *
        ((Formalism.IndefR.Lev.finE (Yc D 0) (embA B.d B.o (a₀ * a)))⁻¹).val := by
    have := (Formalism.IndefR.Lev.finE (D.sp.Y 0)).map_mul (embA B.d B.o (a₀ * a)) (f.g.b 0)
    exact congrArg Units.val ((congrArg Inv.inv this).trans (_root_.mul_inv_rev _ _))
  funext r
  rw [h4, ← mulVec_mulVec]
  have h5 := _root_.GlobalTheory.MiTop.MoveZ.inv_mulVec_adelic_embedding_eq_self W hW B (a₀ * a)
  refine Eq.trans ?_ ((hz r).trans ?_)
  · exact congrArg (fun w => toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ w) r) h5
  · rw [h3, mul_assoc, mul_assoc]
    rfl
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorPairsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_vector_central_twist_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → PuNZ D → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → ∀ u, (∀ φ, ∃ C, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ) ∧ (∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ C, ∃ b, _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ ∧ _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0 := by
  first | exact @_root_.GlobalTheory.MiTop.anchor_pairs_alt | exact _root_.GlobalTheory.MiTop.anchor_pairs_alt | (intros; apply _root_.GlobalTheory.MiTop.anchor_pairs_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutAtOf
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAut
theorem autAt_of_alt (hLab : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal)) (hCof : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite) (hBl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t)) (hSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ) (hAut : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr) →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr)).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ) :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w → AutAt p j P W w := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hr hm j P W hd hn w hw hwr hs
  refine ⟨⟨hLab p hr hm j P W hd hn w hw hwr hs, hCof p hr hm j P W hd hn w hw hwr hs, hBl p hr hm j P W hd hn w hw hwr hs⟩, ?_⟩
  intro _ F R inc T mu θ hmu hE
  obtain ⟨π, hπ, hwt, hl, φ, hφ, hφ0, hQ⟩ := hAut p hr hm j P W hd hn w hw hwr hs F R inc T mu θ hmu hE
  refine ⟨π, hπ, hwt, hl, fun Q => ?_⟩
  have hlab := hLab p hr hm j P W hd hn w hw hwr hs Q
  by_cases hQl : ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal
  · have hun := hl _ (hlab.2.2.2.2 hQl)
    obtain ⟨ψ, hψ, hψ0, hψfix⟩ := hun
    obtain ⟨σ, S, hc, hsat, -⟩ := hSat _ _ π hπ _ hlab.1 ψ hψ hψ0 hψfix
    refine ⟨⟨ψ, hψ, hψ0, hψfix⟩, σ, S, hc, hsat, fun i hi => ?_⟩
    exact absurd (hi ▸ hQl) ((T.ix_range (R.ix i)).1 ⟨i, rfl⟩).2.2
  · obtain ⟨hfix, heig⟩ := hQ Q hQl
    obtain ⟨σ, S, hc, hsat, hk⟩ := hSat _ _ π hπ _ hlab.1 φ hφ hφ0 hfix
    refine ⟨⟨φ, hφ, hφ0, hfix⟩, σ, S, hc, hsat, fun i hi => ?_⟩
    have hle := ((T.ix_range (R.ix i)).1 ⟨i, rfl⟩).2.1
    exact smul_left_injective ℂ hφ0 ((heig i hi).symm.trans (hk _ hle))
theorem autSt_of_alt (hLab : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal)) (hCof : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite) (hBl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t)) (hSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ) (hAut : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr) →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr)).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ) :
    _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  intro hS
  obtain ⟨ε1, he, H⟩ := hS
  refine ⟨ε1, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  refine ⟨K, fun Fm CH hc hl => ?_⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hl
  exact ⟨x0, fun x hx hxx i p hr hm j P W hd hn w hw hwr =>
    _root_.GlobalTheory.FrameAut.autAt_of_alt hLab hCof hBl hSat hAut p hr hm j P W hd hn w hw hwr (hx0 x hx hxx i p hr hm j P W hd hn w hw hwr)⟩
theorem autSt_of_smallSt' : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt :=
  _root_.GlobalTheory.FrameAut.autSt_of_alt _root_.GlobalTheory.T.small_place_block_decomposition_alt _root_.GlobalTheory.T.small_place_finite_set_alt _root_.GlobalTheory.T.norm_sq_emb_block_eq_q_pow_of_small_at GlobalTheory.T.exists_satake_sphericalVector_definiteUnitary _root_.GlobalTheory.T.small_place_prime_local_alt
end GlobalTheory.FrameAut
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseFrTopEq
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.TopFrame
set_option maxHeartbeats 1600000 in
theorem baseFr_top_eq_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i (hm : (J.G i).s + 1 + 1 ≤ B.R.m) (γ : J.Ch₀ ((J.G i).s + 1 + 1)) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((J.G i).s + 1)) (Fin B.R.t) ((J.G i).s + 2) ⊕ Unit ≃ Fin (B.R.N ((J.G i).s + 1 + 1))), GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e → ∀ r b, (ofSplit (J.G i).q).pr (baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b)) = (J.G i).FM.β r b := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat hiA t J hJ i hm γ e he r b
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  have key : ∀ j (h : j = (I.rec7 l Z).R.m), (∀ r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0) ∧
      ∀ r, vecB (a.g.oT j h) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r = if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    intro j h
    subst h
    exact ⟨hiA, fun r => hat.z0 r⟩
  obtain ⟨hA, hz⟩ := key _ (J.G i).hs
  obtain ⟨-, ⟨e', he', hT'⟩, hz0⟩ := ha.stdQ (J.pl i) ⟨t, J.mem i⟩
  let ι : (I.rec7 l Z).host.E →+* (J.G i).k := (J.G i).q.pr.comp (incA (I.rec7 l Z))
  have hL := frsF_top J.A hJ.is hW.tr.ok (J.P i) (hJ.tw i).nmem _ hs γ (finCongr (rankN (I.rec7 l Z) _ hm) r) (e b)
  have hL' : baseFr J.A (J.P i) ((J.G i).s + 1 + 1) hm γ r (e b) =
      if r.val = (e b).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := hL
  have hN : B.R.N ((J.G i).s + 1 + 1) = B.R.N B.R.m := congrArg _ hs
  refine (congrArg _ hL').trans (Eq.trans ?_ (congrFun (congrFun (J.G i).last r) b).symm)
  rcases b with b | b
  · have hb : (e (Sum.inl b)).val = (e' b).val := (he _).trans (he' b).symm
    have hb2 : (e (Sum.inl b)).val + 1 ≠ B.R.N B.R.m := by
      intro h
      have h2 : (e (Sum.inr ())).val = B.R.N B.R.m - 1 := he _
      have h3 : e (Sum.inl b) = e (Sum.inr ()) := Fin.ext (by omega)
      exact Sum.inl_ne_inr (e.injective h3)
    have h5 : (if r.val = (e (Sum.inl b)).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0) =
        (a.g.oT _ (J.G i).hs).iA r (e' b) := by
      refine Eq.trans ?_ (hA r (e' b)).symm
      rw [← hb]
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb2
      · rfl
      · rfl
    refine (congrArg _ h5).trans ?_
    show _ = ∑ c, ι ((a.g.oT _ (J.G i).hs).iA r c) * (J.G i).FT.β c b
    have h6 : ∀ c, (J.G i).FT.β c b = if c = e' b then 1 else 0 := fun c => (congrFun (congrFun hT' c) b).trans Matrix.one_apply
    refine Eq.symm ((Finset.sum_congr rfl fun c _ => congrArg _ (h6 c)).trans ?_)
    refine (Finset.sum_eq_single (e' b) (fun c _ hc => ?_) (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · exact (congrArg _ (if_neg hc)).trans (mul_zero _)
    · exact (congrArg _ (if_pos rfl)).trans (mul_one _)
  · have h2 : (e (Sum.inr b)).val = B.R.N B.R.m - 1 := he _
    have h3 := (e (Sum.inr b)).2
    have h4 : (if r.val = (e (Sum.inr b)).val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0) =
        vecB (a.g.oT _ (J.G i).hs) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r := by
      rw [hz]
      split_ifs with h5 h6 h7
      · rfl
      · omega
      · omega
      · rfl
    refine (congrArg _ h4).trans ?_
    show ι (∑ c, (a.g.oT _ (J.G i).hs).iB r c * (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) c) = ∑ c, ι ((a.g.oT _ (J.G i).hs).iB r c) * (J.G i).z₀ c
    exact (map_sum ι _ _).trans (Finset.sum_congr rfl fun c _ => (map_mul ι _ _).trans (congrArg _ (congrFun hz0 c).symm))
end GlobalTheory.Fam.TopFrame
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotRelTwoStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.botRel_of_botHyp_of_pin_central : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u), d.Pin z → _root_.GlobalTheory.MiTop.BottomRelation W z d := by
  first | exact @_root_.GlobalTheory.MiTop.botRel_of_pin_of_mem_center | exact _root_.GlobalTheory.MiTop.botRel_of_pin_of_mem_center | (intros; apply _root_.GlobalTheory.MiTop.botRel_of_pin_of_mem_center <;> assumption)
end
end

