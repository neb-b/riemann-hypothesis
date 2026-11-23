module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.OpOfProj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0060
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0062
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.CountE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ZEqDimE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OpOpOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem opOf_proj {Λ Γ Q M : Type} [CommRing Λ] [Group Γ] [Group Q] [AddCommGroup M] [Module Λ M]
    (ρ : Representation Λ Q M) (e : Γ ≃* Q) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ.asModule) :
    Module.Projective (MonoidAlgebra Λ Γ) (Representation.asModule (ρ.comp e.toMonoidHom : Representation Λ Γ M)) := by
  let σ : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ Γ := (MonoidAlgebra.domCongr Λ Λ e.symm).toRingEquiv
  let ρ' : Representation Λ Γ M := ρ.comp e.toMonoidHom
  have key : ∀ a : MonoidAlgebra Λ Q, ρ'.asAlgebraHom (σ a) = ρ.asAlgebraHom a := fun a => by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single g c => simp [σ, ρ']
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let f : ρ.asModule ≃ₛₗ[(σ : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ Γ)] ρ'.asModule :=
    { ρ.asModuleEquiv.toAddEquiv.trans ρ'.asModuleEquiv.symm.toAddEquiv with
      map_smul' := fun a m => by
        apply ρ'.asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul]
        simp [Representation.asModuleEquiv_map_smul, key] }
  exact Module.Projective.of_equiv f
private theorem opOf_dc {R G P : Type} [CommRing R] [Group G] [AddCommGroup P] [Module R P] (ρ : Representation R G P)
    (K K1 : Subgroup G) [Fintype (K ⧸ K1.subgroupOf K)] (m : P) (hm : m ∈ fixd ρ K1) :
    dc ρ K K1 1 m = ∑ g : K ⧸ K1.subgroupOf K, ρ (g.out : K) m := by
  let f : K ⧸ K1.subgroupOf K → MulAction.orbit K ((1 : G) : G ⧸ K1) := fun g =>
    ⟨((g.out : K) : G), g.out, congrArg QuotientGroup.mk (mul_one _)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 := QuotientGroup.eq.1 (congrArg Subtype.val hab)
      rw [← a.out_eq', ← b.out_eq']
      exact QuotientGroup.eq.2 h1
    · rintro ⟨_, k, rfl⟩
      refine ⟨(k : K ⧸ K1.subgroupOf K), Subtype.ext ?_⟩
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (k : K ⧸ K1.subgroupOf K))
      have h2 : (((k : K ⧸ K1.subgroupOf K).out : K) : G ⧸ K1) = ((k : G) : G ⧸ K1) := QuotientGroup.eq.2 h1
      exact h2.trans (congrArg (QuotientGroup.mk (s := K1)) (mul_one (k : G)).symm)
  unfold dc
  rw [← finsum_comp f hf, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K1 ((g.out : K) : G)
  show ρ (((g.out : K) : G) : G ⧸ K1).out m = _
  rw [hu, map_mul, Module.End.mul_apply, hm u u.2]
private theorem opOf_tr {Λ R G P Γ σ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group G] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] [Group Γ] [Finite Γ] (ρ : Representation R G P)
    (K K1 : Subgroup G) (hle : K1 ≤ K) [(K1.subgroupOf K).Normal]
    (ρ' : Representation Λ (K ⧸ K1.subgroupOf K) (fixd ρ K1))
    (hρ' : ∀ (u : K) f, (ρ' (u : K ⧸ K1.subgroupOf K) f : P) = ρ u f)
    (hP : Module.Projective (MonoidAlgebra Λ (K ⧸ K1.subgroupOf K)) ρ'.asModule)
    (e : Γ ≃* K ⧸ K1.subgroupOf K) (γ : σ → Γ) (hγ : Subgroup.closure (Set.range γ) = ⊤)
    (Y : σ → Module.End R (fixd ρ K1)) (hY : ∀ p m, ρ' (e (γ p)) m = m + Y p m)
    (tr : fixd ρ K1 →ₗ[R] fixd ρ K) (htr : ∀ m, (tr m : P) = dc ρ K K1 1 m) :
    Function.Surjective tr ∧ LinearMap.ker tr = ⨆ p, LinearMap.range (Y p) := by
  haveI : Finite (K ⧸ K1.subgroupOf K) := Finite.of_equiv Γ e.toEquiv
  letI := Fintype.ofFinite (K ⧸ K1.subgroupOf K)
  obtain ⟨h1, h2⟩ := projNorm Λ _ _ ρ' hP
  have hs : ∀ m, (tr m : P) = (∑ g, ρ' g m : fixd ρ K1) := fun m => by
    rw [htr, opOf_dc ρ K K1 m m.2, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hρ', QuotientGroup.out_eq']
  refine ⟨fun v => ?_, le_antisymm (fun m hm => ?_) (iSup_le fun p => ?_)⟩
  · obtain ⟨m, hm⟩ := h1 ⟨v, fixd_anti ρ hle v.2⟩ fun g => by
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      exact Subtype.ext ((hρ' u _).trans (v.2 u u.2))
    exact ⟨m, Subtype.ext (by rw [hs, hm])⟩
  · have h0 : ∑ g, ρ' g m = 0 := Subtype.ext (by rw [← hs, LinearMap.mem_ker.1 hm]; rfl)
    have hc : Subgroup.closure (Set.range fun p => e (γ p)) = ⊤ := by
      have := congrArg (Subgroup.map e.toMonoidHom) hγ
      rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _ e.surjective] at this
      exact this
    have h3 : (⨆ g ∈ Set.range fun p => e (γ p), LinearMap.range (ρ' g - 1)) ≤
        (⨆ p, LinearMap.range (Y p)).restrictScalars Λ := by
      refine iSup₂_le ?_
      rintro _ ⟨p, rfl⟩ _ ⟨v, rfl⟩
      refine Submodule.mem_iSup_of_mem (p := fun p => LinearMap.range (Y p)) p ⟨v, ?_⟩
      rw [LinearMap.sub_apply, hY, Module.End.one_apply, add_sub_cancel_left]
    exact h3 (h2 _ hc m h0)
  · rintro _ ⟨m, rfl⟩
    have h4 : tr (ρ' (e (γ p)) m) = tr m := Subtype.ext (by
      rw [hs, hs]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulRight (e (γ p))) _ _ fun g => ?_
      rw [Equiv.coe_mulRight, map_mul, Module.End.mul_apply])
    rw [hY, map_add (f := _)] at h4
    exact add_eq_left.1 h4
private theorem opOf_gen {l q n : ℕ} (hl : l.Prime) (a : Fin q → ℕ) :
    Subgroup.closure (Set.range fun p : Fin q × Fin n => (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a)) = ⊤ := by
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  refine eq_top_iff.2 fun g _ => ?_
  rw [← Finset.univ_prod_mulSingle g]
  refine Subgroup.prod_mem _ fun s _ => ?_
  have h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [h1, Pi.mulSingle_pow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self s)) _
private theorem opOf_cop {L : Type} [Field L] [NumberField L] (w : Plc L) {l : ℕ} (hl : l.Prime)
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) : l.Coprime (resCard (w.adicCompletion L)) := by
  have h1 : Valued.v (l : w.adicCompletion L) = 1 := by
    have e : (l : w.adicCompletion L) = algebraMap L _ (algebraMap (𝓞 L) L l) := by simp
    rw [e]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans ?_
    exact (HeightOneSpectrum.valuation_of_algebraMap w _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hw)
  have h2 : valuation (w.adicCompletion L) (l : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 h1
  have h3 : IsUnit (l : 𝒪[w.adicCompletion L]) :=
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 (by simpa using h2)
  have h4 : (l : 𝓀[w.adicCompletion L]) ≠ 0 := by
    simpa using (h3.map (residue 𝒪[w.adicCompletion L])).ne_zero
  rw [hl.coprime_iff_not_dvd]
  intro hd
  letI := Fintype.ofFinite 𝓀[w.adicCompletion L]
  haveI := Fact.mk hl
  rw [resCard, Nat.card_eq_fintype_card] at hd
  exact h4 ((ringChar.spec _ _).2 (by
    have h5 := (prime_dvd_char_iff_dvd_card l).2 hd
    have h6 := CharP.char_is_prime 𝓀[w.adicCompletion L] (ringChar 𝓀[w.adicCompletion L])
    rw [(Nat.prime_dvd_prime_iff_eq hl h6).1 h5]))
private theorem opOf_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwC k n ⊤ := by
  have h1 : unitsC k C ≤ unitsC k ⊤ := Subgroup.map_mono (Subgroup.comap_mono le_top)
  have h2 : torC k n C ≤ torC k n ⊤ := fun t ht i hi => h1 (ht i hi)
  exact sup_le_sup_left (Subgroup.map_mono h2) _
private theorem opOf_tow {Λ R P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] (S : Submodule R P) : IsScalarTower Λ R S := inferInstance
theorem UpperTheory.V.Th.opOfX_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (ph ta : Fin q → (globOf r V).G₀) (N : ℕ), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → (∀ j, qj w j ≡ 1 [MOD l ^ N]) → ∃ A' : OpMod b h q N, OpRelX A' (qj w) ph ta (2 * n.factorial) := by
  intro hP l hl L Ω _ _ _ _ _ _ s V0 O _ _ _ hO _ n r B J D b V h q w A x δ hw hx hδ ph ta N hok hN
  have hq : ∀ j, IsUnit (qj w j : A.R) := fun j => by
    haveI := hO.char
    have h1 : IsUnit (qj w j : ResidueField O) :=
      (CharP.isUnit_natCast_iff hl.out).2 (hl.out.coprime_iff_not_dvd.1 (opOf_cop (w j) hl.out (hw j)))
    have h2 : IsUnit (qj w j : O) := by
      rw [← map_natCast (residue O)] at h1
      exact (isUnit_map_iff _ _).1 h1
    simpa using h2.map (algebraMap O A.R)
  obtain ⟨T⟩ := thEx L n q w l A.R A.P A.ρ x δ hq
  obtain ⟨hn, ρ', hρ', hpr⟩ := A.proj
  obtain ⟨e, he⟩ := delIso L n q w l δ hδ
  obtain ⟨hy, tr, htr, hu⟩ := trOf L n q w l A.R A.P A.ρ x δ T hδ
  have h2 := _root_.UpperTheory.V.Z.Win.T2.level_relation_two_x hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have h3 := _root_.UpperTheory.V.Pa.Lev.twoOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have hg : ∀ j i m, ρ' (e (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1))) m = T.act1 (1 + yV A.R j i) m := fun j i m => by
    obtain ⟨g, hg1, hg2⟩ := he j i
    exact Subtype.ext (by rw [hg2, hρ', hg1]; exact (hy j i m).symm)
  have hle : UIw1 l n w ≤ UIw n w := fun g hg j hj => opOf_le _ (hg j hj)
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ padicValNat l (qj w p.1 - 1)) := fun s => ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨hs, hk⟩ := opOf_tr A.ρ (UIw n w) (UIw1 l n w) hle ρ' hρ' hpr e
    (fun p : Fin q × Fin n => Pi.mulSingle p (Multiplicative.ofAdd 1)) (opOf_gen hl.out fun j => padicValNat l (qj w j - 1))
    (fun p : Fin q × Fin n => T.act1 (yV A.R p.1 p.2)) (fun p m => (hg p.1 p.2 m).trans (by rw [map_add (f := _), map_one]; rfl)) tr htr
  have ha : ∀ j, N ≤ padicValNat l (qj w j - 1) := fun j => by
    have h4 : 1 < qj w j := Finite.one_lt_card
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (by omega)).1 ((Nat.modEq_iff_dvd' h4.le).1 (hN j).symm)
  exact ⟨{ rN := A.rN, compat := A.compat, R := A.R, p := A.p, segmentWeightExponent := A.segmentWeightExponent, β := A.β, β_pair := A.β_pair
           M1 := fixd A.ρ (UC n w fun _ => ellC l _), tow1 := opOf_tow _, fin1 := A.fin, Mw := fixd A.ρ (UC n w fun _ => ⊤)
           act1 := T.act1, actw := T.actw, a := fun j => padicValNat l (qj w j - 1), le_a := ha
           ρ := ρ'.comp e.toMonoidHom, ρ_gen := hg, proj := opOf_proj ρ' e hpr
           tr := tr, tr_surj := hs, tr_ker := hk, tr_u := hu }, h3, h2⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ProjectedFormsLinkOfPrintedHida
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
private theorem part2 (H : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {ι : Qbar l ≃+* ℂ}
    {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (hρ : Continuous ρ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    (hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ) (hi : Af.IsIrr (ρ.comp V.pr)) :
    ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  have hc : Continuous (ρ.comp V.pr) := hρ.comp (V.pr_cont W.continuous_resP)
  have hoff : ∀ᶠ w : Plc L in Filter.cofinite, (l : 𝓞 L) ∉ w.asIdeal := by
    have hspan : Ideal.span {(l : 𝓞 L)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors hspan).subset fun w hw =>
      Ideal.dvd_span_singleton.mpr (not_not.mp hw)
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.link2_alt H L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ _ hc hi
    (hoff.mono fun w hw hsp τ hτ B hB => _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hw hB (hLG w hsp τ hτ))
theorem projected_forms_link_of_printed_hida (H : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ hσ h0
  obtain ⟨Y, hY, -, -, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt H l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ hσ h0
  refine ⟨Y, hY, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := part2 H s hn Y.cont hσ hLG hi
  exact ⟨π, p1, p2, p3, p4, fun w hw τ => (p5 w hw τ).1⟩
end UpperTheory.Gal.projectedFormsSystemPart
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCountE
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing Filter GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem ce_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem ce_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := ce_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
private theorem ce_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
    ext i j
    exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
  rwa [this] at h
private theorem ce_ex {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z : Submodule ℂ M)
    (hf : FiniteDimensional ℂ Z) (hZ : Z ≠ ⊥) (hsum : Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z)) :
    ∃ i, Y i ⊓ Z ≠ ⊥ := by
  by_contra h
  push Not at h
  apply hZ
  rw [← Submodule.finrank_eq_zero, hsum]
  exact Finset.sum_eq_zero fun i _ => by rw [h i, finrank_bot]
private def ce_mk {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {n : ℕ} {s : HidaSetting l L Ω} (V : s.Lev) (hS : ∀ v ∈ s.S, IsSplitAt (s.w v)) (τ : ∀ w : Plc L, SmIrr (GLw n w))
    (σ : Submodule ℂ (UA L n → ℂ)) (h : ∀ w, IsSplitAt w → Cp σ w (τ w)) : Comps V σ where
  l v := τ (s.w v.1)
  u v := τ (s.w v)
  o := τ (s.w s.v0)
  hl v := h _ (hS _ (Or.inl v.2))
  hu v := h _ (hS _ (Or.inr (Or.inl v.2)))
  ho := h _ (hS _ (Or.inr (Or.inr rfl)))
private theorem ce_ne {M : Type} [AddCommGroup M] [Module ℂ M] {Y Z : Submodule ℂ M} (h : Y ⊓ Z ≠ ⊥) : Y ≠ ⊥ :=
  fun h' => h (by rw [h', bot_inf_eq])
section Set
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l}
  {H : HSet L Ω l n c} {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] {θ : H.X.I.T →* Aˣ} {ι : Qbar l ≃+* ℂ}
  {x : A →+* Qbar l} {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} {c0 : ℕ}
  {sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d}
private theorem ce_fin (hsp : H.IsSpec θ ι x lam ξ c0 sp) (K : H.Lev) (ev : H.Op → ℂ) :
    FiniteDimensional ℂ (zPart H θ ι x lam ξ K c0 ev) :=
  haveI := hsp.fin K c0 le_rfl
  Submodule.finiteDimensional_of_le (S₂ := H.ClAt θ ι x lam ξ K c0) (inf_le_left.trans (iSup_le fun _ => inf_le_left))
private theorem ce_one (hSl : Slope) (hO1 : _root_.UpperTheory.V.Z.J.D.Ord1Alt) (hEP : EigPi) (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hAx : H.Ax)
    (hsp : H.IsSpec θ ι x lam ξ c0 sp) (ev : H.Op → ℂ) (hev : ∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1)
    (τ : ∀ v, SmIrr (GLw n (H.Sl v))) :
    Module.rank ℂ (eigL H.Sl (piRep fun v => (τ v).ρ) c0 (fun v i y => (ι (H.finPart θ x lam v i y))⁻¹)
      fun v j => H.lowVal ι lam v (j + 1) * ev (.inr (v, j))) ≤ 1 := by
  refine hEP L n H.V H.Sl τ c0 _ _ fun v => ?_
  refine hO1 N _ n _ _ (τ _).smooth (τ _).irred c0 _ _ (fun i y hy => ?_)
    (hSl L Ω l n c H hAx ι lam v (fun j => ev (.inr (v, j))) (hev v))
  rw [hsp.triv v i y hy, map_one, inv_one]
end Set
section Stg
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (s : HidaSetting l L Ω)
private theorem ce_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)
private theorem ce_split (w : Plc L) (h : w.under (𝓞 (Lp L)) ∈ s.S) : IsSplitAt w :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A _) _ (s.hA _) (s.split _ h) w rfl
private theorem ce_S (v : Plc (Lp L)) (h : v ∈ s.S) : IsSplitAt (s.w v) := ce_split s _ ((ce_w s v).symm ▸ h)
private theorem ce_irr (V : s.Lev) {n : ℕ} (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (hi : Af.IsIrr ρ) : Af.IsIrr (ρ.comp V.pr) := by
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, ReciprocityTheory.Gal.toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨t, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨t, Subtype.ext hτ⟩
  refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => ?_⟩
  obtain ⟨g, rfl⟩ := hpr g
  exact hI g
end Stg
private theorem eigenpart_zero_eq_top {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ (0 : G →₀ ℤ) 0 = ⊤ := by
  simp [ePart, opE]
private theorem ce_top {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z E : Submodule ℂ M) (hE : E = ⊤)
    (hsum : Module.finrank ℂ ↥(Z ⊓ E) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E)) :
    Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z) := by
  subst hE
  have h : ∀ S : Submodule ℂ M, Module.finrank ℂ ↥(S ⊓ ⊤) = Module.finrank ℂ S := fun S => by rw [inf_top_eq]
  simpa only [h] using hsum
private theorem cardinal_factor_eq_one {M : Type} [AddCommGroup M] [Module ℂ M] (Y Z ZL E : Submodule ℂ M) (hE : E = ⊤) (h0 : Y ⊓ Z ≠ ⊥) (h2 : Y ⊓ Z = Y ⊓ ZL)
    (a b : Cardinal) (ha : a ≤ 1) (h3 : Module.rank ℂ ↥(Y ⊓ ZL ⊓ E) = a * b) : a = 1 := by
  subst hE
  rcases Cardinal.le_one_iff.1 ha with h | h
  · rw [h, zero_mul, Submodule.rank_eq_zero, inf_top_eq, ← h2] at h3
    exact absurd h3 h0
  · exact h
private theorem ce_cnt {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z ZL E : Submodule ℂ M)
    (hf : FiniteDimensional ℂ Z) (hsum : Module.finrank ℂ ↥(Z ⊓ E) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E)) (P : J → Prop)
    (a b : Cardinal) (k : ℕ) (h1 : ∀ i, Y i ⊓ Z ≠ ⊥ → P i) (h2 : ∀ i, P i → Y i ⊓ Z = Y i ⊓ ZL) (ha1 : a = 1)
    (h3 : ∀ i, P i → Module.rank ℂ ↥(Y i ⊓ ZL ⊓ E) = a * b) (hk : Nat.card {i // P i} = k) :
    (Module.finrank ℂ ↥(Z ⊓ E) : Cardinal) = k * b := by
  classical
  have h6 : ∀ i, (Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E) : Cardinal) = if P i then b else 0 := fun i => by
    haveI : FiniteDimensional ℂ ↥(Y i ⊓ Z ⊓ E) := Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_right)
    rw [Module.finrank_eq_rank]
    split_ifs with h
    · rw [h2 i h, h3 i h, ha1, one_mul]
    · rw [Submodule.rank_eq_zero]
      by_contra h'
      refine h (h1 i fun h'' => h' ?_)
      rw [h'', bot_inf_eq]
  rw [hsum, Nat.cast_sum, Finset.sum_congr rfl fun i _ => h6 i, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hk,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.Desc.V0.count_e_of_sph_same_at_same_bc_dims :
    UpperTheory.V.Z.J.D.WtEx → UpperTheory.V.Z.J.D.Decomp → ZDecE → UpperTheory.V.Z.J.D.ZEq → _root_.UpperTheory.V.Z.J.D.SphSameAlt → _root_.UpperTheory.V.Z.J.D.AtSameAlt → _root_.UpperTheory.V.Z.J.D.BcOfAlt → YDimE → UpperTheory.V.Z.J.D.CompsEx → UpperTheory.V.Z.J.D.Slope → _root_.UpperTheory.V.Z.J.D.Ord1Alt → UpperTheory.V.Z.J.D.EigPi → _root_.UpperTheory.V.Z.Desc.V0.CountEAlt := by
  intro hWt hDec hZD _ hSph hAt hBc hYD _ hSl hO1 hEP PH hM hCO l _ L Ω _ _ _ _ _ _ s n hn V hV h4 ι lam
  have N := PH.toClassicalTheorems.litN
  have hU : GlobalTheory.BCT.Unr L := UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr
  obtain ⟨lam', hl'⟩ := hWt l L Ω s n hn V hV ι lam
  obtain ⟨a₀, -, ha⟩ := hM L hU n hn h4 lam'
  refine ⟨a₀, ?_⟩
  intro Q c r m τ₀ hτ d e ξ he A _ _ _ θ x c0 sp hθ hsp K ev hev hZ hP
  have hAx := _root_.UpperTheory.V.Hi.axU_s N l L Ω s n hn V Q c m τ₀
  have hS := ce_S s
  obtain ⟨t, ht⟩ := ce_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    ce_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  obtain ⟨S, K', J, _, σ, hSec, hLev, hKL, hID, hInd, hUn, hFix, hLe⟩ :=
    hDec l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he hop lam' hl' c0
  have hA : ∀ i, IsAutRepU (σ i) := fun i => (hID.1 i).1
  have hsumE := fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) (h : ∀ g ∈ a.support, g ∈ KO _ (Fin n)) =>
    hZD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev J σ hA hInd hLe a N h
  have he0 : eC Q τ₀ d (0 : GLw n (s.w s.v0) →₀ ℤ) 0 = ⊤ := eigenpart_zero_eq_top _
  have hsum := ce_top (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ he0 (hsumE 0 0 (by simp))
  have hfin := ce_fin hsp K ev
  obtain ⟨i0, h0⟩ := ce_ex (fun i => YOf Q ι τ₀ e ξ (σ i)) _ hfin hZ hsum
  have hY0 : YOf Q ι τ₀ e ξ (σ i0) ≠ ⊥ := ce_ne h0
  obtain ⟨Y, hY, -, -, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt PH l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he (σ i0) (hA i0) hY0
  have hi := hP Y (by rw [hY]; exact h0)
  have hc : Continuous (Y.r.comp V.pr) := Y.cont.comp (V.pr_cont W.continuous_resP)
  obtain ⟨π, hreg, hcsd, hat, hinf, hsat⟩ := hBc PH L Ω hU l s.odd ι n hn (σ i0) (hA i0) (Y.r.comp V.pr) hc (ce_irr s V Y.r hi)
    (Eventually.of_forall hLG)
  have hns : ∀ w : Plc L, ¬ IsSplitAt w → w.under (𝓞 (Lp L)) ∉ s.S := fun w h h' => h (ce_split s w h')
  choose τ hτπ using fun w => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PH.toClassicalTheorems L n π w).1
  have hCp : ∀ i, At π (σ i) → ∀ w, IsSplitAt w → Cp (σ i) w (τ w) := fun i h w hw =>
    hCO L hU n hn h4 π hreg hcsd (σ i) (hA i) (fun w hw => hUn i w (hns w hw)) h w hw _ (hτπ w)
  have hcard := ha π hreg hcsd (fun v => hinf _ _ ((hID.1 i0).2.1 v)) (fun w hw => hsat w (hUn i0 w (hns w hw))) S hSec K' hLev
    (fun w hw => hKL w (hns w hw)) (fun w hwS hw => ⟨τ w, hτπ w, hFix i0 w hwS hw _ (hCp i0 hat w hw)⟩) J σ hID
  have h1 := fun i h => hAt N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev _ _ (hA i0) (hA i) h0 h π hat
  have h2 := fun i (h : At π (σ i)) => hSph N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev _ _ (hA i0) (hA i)
      (fun w hw => ⟨τ w, hCp i0 hat w hw, hCp i h w hw⟩) h0
  have h3 := fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) i (h : At π (σ i)) =>
    hYD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he (σ i) (hA i) (hUn i) ((hl' _ (hA i)).2 (hID.1 i).2.1)
      (ce_mk V hS τ (σ i) (hCp i h)) c0 (fun v i y => (ι ((hset Q τ₀).finPart θ x.toRingHom lam v i y))⁻¹)
      (fun v j => (hset Q τ₀).lowVal ι lam v (j + 1) * ev (.inr (v, j))) a N
  have h5 := ce_one hSl hO1 hEP N hAx hsp ev hev fun v => τ (s.w v.1)
  have ha1 := cardinal_factor_eq_one _ _ _ _ he0 h0 (h2 i0 hat) _ _ h5 (h3 0 0 i0 hat)
  refine ⟨π, σ i0, ce_mk V hS τ (σ i0) (hCp i0 hat), fun u => hτπ _, hτπ _, hY0, hA i0, fun a N' hs => ?_⟩
  exact ce_cnt (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ _ hfin (hsumE a N' hs) (fun i => At π (σ i)) _ _ a₀ h1 h2 ha1 (h3 a N') hcard
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOutRep
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem mem_lev {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)}
    (hS : Places (S : Set (Plc L))) (hK : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (iw w).J n) : x ∈ lev U S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hJ
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨hK w hw ⟨hx, hk⟩, fun w' hw' => ?_⟩
  by_cases e : w' = w
  · subst e; exact hJ
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' hw h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
    exact one_mem _
theorem UpperTheory.V.Z.Sym.Al.outRep_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U →
        ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ) ∧
          ∀ S : Finset (Plc L), Places (S : Set (Plc L)) → (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) →
          ∀ (ψ : ∀ w : Plc L, Fin n → (Kw w)ˣ →* ℂˣ) (φ : UA L n → V), φ ≠ 0 → IsAF R (lev U S iw) φ →
          (∀ w ∈ S, (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ w i u = 1) ∧ (∀ i i', i ≠ i' → ψ w i ≠ ψ w i' ∧ ψ w i ≠ ψ w i' * absPow (Kw w) 1) ∧
            EigT φ w (iw w) (ψ w)) → ∃ σ ∈ A, ∀ w ∈ S, CompSub σ w (ψ w) := by
  intro H L _ _ _ unr n hn V _ _ _ R hR U hU
  obtain ⟨A, hA, hA', h⟩ := finFam L n V R hR U hU
  refine ⟨A, hA, hA', fun S hS hK ψ φ h0 hφ hψ => ?_⟩
  obtain ⟨π, φ₁, hπ, h1, hφ₁, hc, he⟩ := proj L n V R hR _ ((cof L n).2.2.1 U hU S iw) φ h0 hφ
  have hcs : ∀ w ∈ S, CompSub π w (ψ w) := fun w hw =>
    _root_.UpperTheory.V.Z.Sym.Al.comp_sub_of_eigen_vector_fixed_by_j H L unr n hn V π hπ w (hS.split w hw) φ₁ h1 hc (fun x hx hJ => hφ₁.level x (mem_lev hS hK hw hx hJ)) (ψ w)
      (fun i => (unrSmooth _).1 _ ((hψ w hw).1 i)) fun d hd => he _ _ _ _ ((hψ w hw).2.2 d hd)
  obtain ⟨φ₂, h2, hc2, hφ₂⟩ := raise L n V R π hπ U hU.1 S hS
    (fun w hw => ⟨hK w hw, _root_.UpperTheory.V.Z.Sym.Al.unramified_of_split_distinct_characters H L n π w (ψ w) (hS.split w hw) (hcs w hw) (hψ w hw).1 (hψ w hw).2.1⟩) iw φ₁ h1 hc hφ₁
  obtain ⟨σ, hσ, ht⟩ := h π hπ φ₂ h2 hφ₂ hc2
  refine ⟨σ, hσ, fun w hw => ?_⟩
  obtain ⟨a, τ, b, c⟩ := hcs w hw
  exact ⟨a, τ, ht w τ b, c⟩
end
end

