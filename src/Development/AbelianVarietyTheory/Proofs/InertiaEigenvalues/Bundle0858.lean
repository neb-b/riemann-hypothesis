module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstOfCrys

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem mulV_crisIncl_comm {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] (c : ↥(MaximalUnramifiedExtension l)) (x : P.R.B ⊗[ℚ_[l]] V) :
    mulV P LL V c (crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V x)) =
      crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c • x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul, crisIncl_tmul, crisIncl_tmul,
      mulV_tmul, Polynomial.algebraMap_apply, smul_eq_mul, C_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem isPst_of_isCrys (T : LocTied l P AI) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (hc : IsCrys (P.PD K) ρ) : IsPst P ρ := by
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.Per.TiedRestrict.fracInv_of_tied T K
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg ρ
  obtain ⟨hfin, -⟩ := GlobalTheory.RegularRing.finite_le₀ (P.PD K) hf ρ
  have hd := (GlobalTheory.RegularRing.isCrys_iff_finrank (P.PD K) ρ).1 hc
  let e := set_option synthInstance.maxHeartbeats 200000 in
    Module.finBasisOfFinrankEq ↥(K0 K) _ hd
  have hB := GlobalTheory.RegularRing.indepB (P.PD K) hf ρ e e.linearIndependent
  have hmem : ∀ i, crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V (e i : P.R.B ⊗[ℚ_[l]] V)) ∈ Dpst P ρ := by
    intro i
    refine (mem_Dpst P ρ).mpr ⟨K, fun g _ => ?_⟩
    rw [stRep_crisIncl]
    congr 1
    exact (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris (PD := P.PD K) ρ _).1 (e i).2 g
  let y : Fin (finrank ℚ_[l] V) → DpstUr P ρ := fun i => toUr P ρ ⟨_, hmem i⟩
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = 0 := by
      rw [hc]; rfl
    have h2 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
        crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V
          (∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Submodule.coe_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mulV_crisIncl_comm]
      rfl
    rw [h2] at h1
    have h3 : ∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V) = 0 :=
      (TensorProduct.comm ℚ_[l] P.R.B V).injective
        (crisIncl_injective P (h1.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    have h4 := Fintype.linearIndependent_iff.1 hB (fun j => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j)) h3 i
    exact (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h4.trans (map_zero _).symm)
  have hlow : (finrank ℚ_[l] V : Cardinal) ≤ Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
    have := hli.cardinal_le_rank
    rwa [Cardinal.mk_fintype, Fintype.card_fin] at this
  have hV : Module.rank ℚ_[l] V = (finrank ℚ_[l] V : Cardinal) := (Module.finrank_eq_rank ℚ_[l] V).symm
  rw [IsPst, hV]
  exact le_antisymm hup hlow

end GlobalTheory.PstOfCrys

namespace GlobalTheory.PstOfCrys

theorem pst_of_pc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) := by
  intro D i w hw K' h hN hF hS m r _ hpc
  let r' : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin m) ↥(D.nbr i w hw).LL.1 :=
    mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))
  have hmodel : IsModel (D.nbr i w hw)
      (resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) (D.nbr i w hw).LL r' := by
    refine ⟨le_rfl, ?_⟩
    ext g a b
    exact ((D.loc_tie i w hw).1 _).symm
  refine ⟨(D.nbr i w hw).LL, r', hmodel, ?_⟩
  have hc := ((GlobalTheory.PcRes.main _ (D.loc (D.nd.l i)) _ K' (D.nbr i w hw).LL h hN hF hS _ _).2).1 hpc
  have hp := isPst_of_isCrys (D.locT (D.nd.l i)) _ hc
  exact (GlobalTheory.PstLaws.isPst_resTo_iff (D.loc (D.nd.l i)) _ h).1 hp

end GlobalTheory.PstOfCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZero
section
noncomputable section

namespace GlobalTheory.RegType

section Fin

open Polynomial GlobalTheory.GLq Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT CategoryTheory

variable {g : ℕ} [Fact g.Prime]

def datum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : LabelDatum g where
  teich := t
  teich_inj := ht
  gen := ζ
  gen_order d hd := (hζ d hd).1
  gen_norm d e hd he := (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

variable {t : Formalism.CyclotomicNorms.Fbar g →* ℂ} {ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y}
  {ζ : ℕ → Formalism.CyclotomicNorms.Fbar g} {hζ : IsGenSys ζ} (O : LabelMap (ZMod g) (convC t ht ζ hζ))
  (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → Simple τ → IsCuspidal (ZMod g) τ →
    HasCuspLabel (convC t ht ζ hζ) τ (O.lab d τ))
include hO

theorem isCuspOf_lab (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (hd : 1 ≤ d) (hs : Simple V)
    (hc : IsCuspidal (ZMod g) V) : IsCuspOf (datum t ht ζ hζ) (O.lab d V) (fun x => V.character x) :=
  _root_.GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel g (datum t ht ζ hζ) t ht hζ rfl d V _ hd ((_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hs).2 hc) (hO d V hd hs hc)

theorem allLab : AllLab (datum t ht ζ hζ) := by
  intro d χ hχ
  obtain ⟨V, hV, hVχ⟩ := hχ.2.1
  obtain rfl : (fun x => V.character x) = χ := funext hVχ
  exact ⟨_, isCuspOf_lab O hO d V hχ.1 hV ((_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hχ.1 hV).1 hχ)⟩

theorem eSerC_mul_zIdem {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod g))) (hρ : Simple ρ) (f : (ZMod g)[X])
    (h : zIdem ρ * eSerO O r f = zIdem ρ) : eSerC (datum t ht ζ hζ) r f * zIdem ρ = zIdem ρ := by
  classical
  by_cases hm : zIdem ρ ∈ GlobalTheory.SerOSys.Zl O r f
  · obtain ⟨τ, hτ, he, hl⟩ := hm
    have h1 := _root_.GlobalTheory.SerCmp.hasLabel_of_hasLabelO g (datum t ht ζ hζ) O (isCuspOf_lab O hO) (_root_.GlobalTheory.HCChar.trace_hcRep_eq_hcL g) (_root_.GlobalTheory.GLq.ConstIff.constituent_hcRep_iff g) r τ f hτ hl
    have h2 : zOf (fun x => τ.character x) = zIdem τ := by
      unfold zOf zIdem
      simp only [FDRep.char_one]
      rfl
    have h3 := eSerC_mul_zOf (datum t ht ζ hζ) ⟨τ, hτ, fun _ => rfl⟩ h1
    rwa [h2, he] at h3
  · have h0 : zIdem ρ = 0 := by
      rw [← h, GlobalTheory.SerOSys.eSerO_eq_sum, Finset.mul_sum]
      refine Finset.sum_eq_zero fun z hz => ?_
      have hz' := (GlobalTheory.SerOSys.Zl_finite O r f).mem_toFinset.1 hz
      rw [GlobalTheory.SerOSys.mul_of_mem ⟨ρ, hρ, rfl⟩ (GlobalTheory.SerOSys.Zl_sub O r f hz'), if_neg]
      rintro e
      exact hm (e ▸ hz')
    rw [h0, mul_zero]

end Fin

section Loc

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
  (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

theorem val_lt_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one, Valued.toNormedField.norm_lt_one_iff]

theorem val_le_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.le_one_iff_le_one, Valued.toNormedField.norm_le_one_iff]

include hi in
theorem val_int_le (z : ℤ_[g]) : valuation (w.adicCompletion E) (i (z : ℚ_[g])) ≤ 1 :=
  (val_le_iff _).2 (GlobalTheory.TypeRec.Model.emb_le w g i.toRingHom hi _ z.2)

include hw hi in
theorem val_int_lt (z : ℤ_[g]) (hz : PadicInt.toZMod z = 0) : valuation (w.adicCompletion E) (i (z : ℚ_[g])) < 1 := by
  have h1 : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [PadicInt.coe_mul, map_mul, map_mul, PadicInt.coe_natCast, map_natCast]
  exact mul_lt_one_of_nonneg_of_lt_one_right (val_int_le i hi c) zero_le
    ((val_lt_iff _).2 (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w g hw))


include hw hi in
theorem act_lift {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : IsLevelOne π x)
    (k : GL (Fin n) ℤ_[g]) (h : GL (Fin n) (w.adicCompletion E)) (hh : IsLiftN (red g n k) h) :
    π h x = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k)) x := by
  set K := Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) with hK
  have h1 : IntM (K⁻¹).val := fun a b => by
    rw [hK, ← map_inv, ← map_inv]
    exact val_int_le i hi ((k⁻¹).val a b)
  have h2 : MaxM (h.val - K.val) := fun a b => by
    have e1 := hh a b
    rw [dite_eq_left ⟨a.2, b.2⟩] at e1
    have e2 := val_int_lt hw i hi ((((red g n k).val a b).val : ℤ_[g]) - k.val a b) (by
      rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]; rfl)
    have e3 := Valuation.map_add_lt _ e1 e2
    convert e3 using 2
    rw [PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast, Matrix.sub_apply]
    change _ - i (k.val a b : ℚ_[g]) = _
    ring
  have h3 : π (K⁻¹ * h) x = x := hx _ fun a b => by
    have e := h1.mul_maxM h2 a b
    rw [Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.sub_apply,
      Matrix.one_apply] at e
    exact e
  conv_rhs => rw [← h3]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

include hw hi in
theorem mem_principalCongruenceFixed_of_levelOne {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : IsLevelOne π x) :
    x ∈ fixK1 (π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) := by
  refine (Model.mem_principalCongruenceFixedVectors_iff _ _).2 fun k hk => ?_
  have := act_lift hw i hi π hx k 1 (fun a b => by
    rw [dite_eq_left ⟨a.2, b.2⟩, hk]
    by_cases hab : a = b
    · subst hab; simp [ZMod.val_one]
    · simp [Matrix.one_apply_ne hab])
  rw [map_one] at this
  exact this.symm

include hw hi in
theorem actK_ne_of_notKilled {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : IsLevelOne π x)
    (z : MonoidAlgebra ℂ (Gn g n)) (hz : NotKilled π z x) :
    actK (π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) z x ≠ 0 := by
  obtain ⟨ℓ, hℓ, h0⟩ := hz
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at h0
  rw [actK, LinearMap.sum_apply]
  convert h0 using 2 with y
  have e : red g n (Function.invFun (red g n) y) = y := Function.invFun_eq (Model.red_surjective n y)
  rw [LinearMap.smul_apply, act_lift hw i hi π hx (Function.invFun (red g n) y) (ℓ y) (by rw [e]; exact hℓ y)]
  rfl

theorem has_of_actK (S : Sys g) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {x : V} (hx : x ∈ fixK1 π) {z : MonoidAlgebra ℂ (Gn g n)}
    (hz : actK π z x ≠ 0) {f : (ZMod g)[X]} (he : S.e n f * z = z) : Has S π f := by
  refine ⟨_, ((repK π).asAlgebraHom z ⟨x, hx⟩).2, ?_⟩
  rw [← repK_alg π (S.e n f) ((repK π).asAlgebraHom z ⟨x, hx⟩), ← Module.End.mul_apply, ← map_mul, he, repK_alg]
  exact hz

variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : IsRec h rc) (hDZ : GlobalTheory.Published.DepthZeroInertia)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ

end Loc

end GlobalTheory.RegType

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterTwistUniversalCharAtChosenPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ResTwist

theorem res_twist_spec : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (x : (kP PP.1)ˣ),
      (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 x : ℂˣ) : ℂ) =
        ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i)
          (Pi.single PP (Multiplicative.toAdd ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 x))))) : (X.Ok i k)ˣ) : X.Ok i k) := by
  intro D N X ρ hρ Y hY i b k Q M χ hT PP x
  let χc : Multiplicative (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) →* Circle :=
    unitPart.comp ((Units.map (ρ.eOk i b k).toMonoidHom).comp (χ.comp (AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i)))))
  have hgood := GlobalTheory.UnivGood.univOf_good D N X ρ hρ Y i Q M

  have hchar : charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) = χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) := by
    ext1 y
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym y
    have hψ : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
      Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker) (fun g hg => by simp [MonoidHom.mem_ker.1 hg]) (Y.delU_open i Q M)
    have hco : ∀ P : Pl D.host.E, IsOpen ((coord Y i (admissibleConjugatePairPlaces X i Q M) M P).ker : Set (G D.host.E N.Om)) := by
      intro P
      by_cases hP : P ∈ admissibleConjugatePairPlaces X i Q M
      · refine Subgroup.isOpen_mono (H₁ := (Y.delU i (admissibleConjugatePairPlaces X i Q M) M).ker) (fun g hg => ?_) (Y.delU_open i (admissibleConjugatePairPlaces X i Q M) M)
        refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
        rw [coord_apply Y i (admissibleConjugatePairPlaces X i Q M) M hP, MonoidHom.mem_ker.1 hg]
        rfl
      · rw [coord, dite_eq_right hP]
        simp
    have e1 : (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) y = Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
      change Multiplicative.ofAdd (fun PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) y)) = _
      congr 1
      funext P
      exact congrArg Multiplicative.toAdd (ρ.rc.pull_eq (hco P.1) hσ)
    have e2 : Y.delU i Q M σ = AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i))
        (Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ)) :=
      Multiplicative.toAdd.injective (delU_eq_spread hY (twSet_of_twOK hT) (hρ.ch i) σ)
    simp only [charOf, MonoidHom.comp_apply]
    rw [ρ.rc.pull_eq hψ hσ, e1, MonoidHom.comp_apply, e2]
    rfl
  have hspec := GlobalTheory.ExportSeries.SpecGood.spec_good D (ZMod (X.l i ^ M)) Circle (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc hgood
  have hres : IsResAt (χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)))) PP.1 (((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1) := hspec.res PP.1 PP.2
  have hidem := hgood.1.isIdemAt PP.2
  have htres : (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 = ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 := by
    change resOf (charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M))) PP.1 = _
    rw [hchar]
    exact GlobalTheory.ConjTwist.isResAt_unique hidem (isResAt_resOf ⟨_, hres⟩) hres
  have hs : ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 = χc.comp ((AddMonoidHom.toMultiplicative
      (AddMonoidHom.single (fun _ : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => ZMod (X.l i ^ M)) ⟨PP.1, PP.2⟩)).comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1)) := dif_pos PP.2
  have hz : ∀ z : Multiplicative (DelQM D.host (X.l i) Q M), z ^ (X.l i ^ M) = 1 := by
    intro z
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul]
    refine congrArg Multiplicative.ofAdd (funext fun v => ?_)
    simp [nsmul_eq_mul, ZMod.natCast_self]
  change (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 x : Circle) : ℂ) = _
  rw [htres, hs]
  simp only [χc, MonoidHom.comp_apply]
  rw [unitPart_of_pow (n := X.l i ^ M) (pow_ne_zero _ (X.lPrime i).out.ne_zero)
    (by rw [← map_pow, ← map_pow, hz, map_one, map_one])]
  rfl

end GlobalTheory.ResTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireGood
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.RSnmGood

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def contGood : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Continuous F ∧ GlobalTheory.MSpanDecay.Good F}
  zero_mem' := ⟨continuous_const, (GlobalTheory.MSpanDecay.goodSub E a).zero_mem⟩
  add_mem' := fun h h' => ⟨h.1.add h'.1, (GlobalTheory.MSpanDecay.goodSub E a).add_mem h.2 h'.2⟩
  smul_mem' := fun z _ h => ⟨h.1.const_smul z, (GlobalTheory.MSpanDecay.goodSub E a).smul_mem z h.2⟩

theorem mspanR_le_contGood (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) :
    GlobalTheory.JSW.mspanR π ≤ contGood E a := by
  refine sInf_le ⟨fun φ hφ => ?_, fun F hF h => ?_, fun F hF X _ ν hν k γ hk => ?_⟩
  · exact ⟨(GlobalTheory.RSnm.mem_goodFns ha hπ (Submodule.mem_sup_left ⟨φ, hφ, rfl⟩)).1, GlobalTheory.MSpanDecay.good_of_mem hπ hφ⟩
  · exact ⟨hF.1.comp (continuous_id.mul continuous_const), GlobalTheory.RtGood.good_mul_right E a F h hF.2⟩
  · haveI := hν
    refine ⟨?_, GlobalTheory.MSpanDecay.Good.kernel hF.2 hk⟩
    exact (GlobalTheory.JSW.kerOp_integrable_continuous E a X ν k γ hk ⟨F, hF.2.1⟩ hF.1
      (GlobalTheory.RSnm.bounded_of_decays ha hF.2.decays)).2

theorem mspanR_le_goodFns (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) :
    GlobalTheory.JSW.mspanR π ≤ GlobalTheory.RSnm.goodFns a := fun F hF =>
  ⟨(mspanR_le_contGood ha hπ hF).1, (mspanR_le_contGood ha hπ hF).2.decays,
    (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ.contra (GlobalTheory.JSW.invT_mem_mspanR_contra E a π F hF)).decays⟩


open GroundTheory.Automorphic in
theorem rsIntegral_entire_good {m n : ℕ} (hm0 : 0 < m) (hmn : m < n) {φ : GA E n → ℂ} (g1 : φ ∈ GlobalTheory.RSnm.goodFns n)
    {φ' : GA E m → ℂ} (g2 : φ' ∈ GlobalTheory.RSnm.goodFns m) {F : (Fin m → Ad E) → ℂ}
    (hF : F ∈ GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m)) (μ : Measure (GA E m)) [μ.IsHaarMeasure] {𝓕 : Set (GA E m)}
    (h𝓕 : IsFundamentalDomain (ratGL E m).range 𝓕 μ) :
    (∀ s : ℂ, IntegrableOn (GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s) 𝓕 μ) ∧
      ∀ s : ℂ, AnalyticAt ℂ (fun s => ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s h ∂μ) s := by
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.RSnm.bounded_of_decays (hm0.trans hmn) g1.2.1
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.RSnm.bounded_of_decays hm0 g2.2.1
  set A : GA E m → ℂ := fun h => FourierWhittaker.partialCoeff (GlobalTheory.RSnm.colSmooth m F φ) (m + 1)
    (FourierWhittaker.blockGL hmn.le h) * (starRingEnd ℂ) (φ' h)
  have hAc : Continuous A :=
    ((FourierWhittaker.continuous_partialCoeff (GlobalTheory.RSnm.continuous_colSmooth hF g1.1 hC₁) (m + 1)).comp
      (GlobalTheory.RSnm.continuous_blockGL hmn.le)).mul (Complex.continuous_conj.comp g2.1)
  have hbd : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖A h‖ ≤ C * (min (GlobalTheory.RSnm.detAbs h) (GlobalTheory.RSnm.detAbs h)⁻¹) ^ N := by
    intro N
    obtain ⟨C, hC⟩ := GlobalTheory.RSnm.colSmooth_bound hmn g1 hF N
    refine ⟨C * C₂, fun h => ?_⟩
    have hP := GlobalTheory.RSnm.partialCoeff_bound hmn (b := fun t => C * (min t t⁻¹) ^ N) hC (n - (m + 1)) (m + 1) (by omega)
      le_rfl _ (GlobalTheory.RSnm.inS_blockGL hmn h)
    simp only [GlobalTheory.RSnm.detAbs_blockGL] at hP
    rw [norm_mul, Complex.norm_conj]
    calc _ ≤ C * (min (GlobalTheory.RSnm.detAbs h) (GlobalTheory.RSnm.detAbs h)⁻¹) ^ N * C₂ :=
          mul_le_mul hP (hC₂ h) (norm_nonneg _) ((norm_nonneg _).trans hP)
      _ = _ := by ring
  obtain ⟨hI, hD⟩ := GlobalTheory.T.mellinType_integral_entire_of_rapid_decay (μ.restrict 𝓕) A GlobalTheory.RSnm.detAbs hAc.aestronglyMeasurable
    GlobalTheory.RSnm.continuous_detAbs.measurable GlobalTheory.RSnm.detAbs_pos (_root_.GlobalTheory.FinVolGL.integrableOn_min_absDet E m hm0 μ 𝓕 h𝓕) hbd
  have e : ∀ s, GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s =
      fun h => A h * ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ (s - ((n : ℂ) - m) / 2) := fun s => rfl
  refine ⟨fun s => by rw [e]; exact hI _, fun s => ?_⟩
  simp only [e]
  exact (hD.analyticAt _).comp (analyticAt_id.sub analyticAt_const)

end GlobalTheory.RSnmGood
end
end

