module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsExist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.Cong.SphOpsProof

open GlobalTheory.LFun Formalism.UG GlobalTheory.Cong.OpPoly

def zq (q : ℕ) (hq : q ≠ 0) : Subring ℂ where
  carrier := {x | ∃ (m : ℤ) (e : ℕ), x = (m : ℂ) / (q : ℂ) ^ e}
  mul_mem' := by
    rintro _ _ ⟨m, e, rfl⟩ ⟨m', e', rfl⟩
    refine ⟨m * m', e + e', ?_⟩
    push_cast
    rw [pow_add, div_mul_div_comm]
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, e, rfl⟩ ⟨m', e', rfl⟩
    have h0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    refine ⟨m * (q : ℤ) ^ e' + m' * (q : ℤ) ^ e, e + e', ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨m, e, rfl⟩
    exact ⟨-m, e, by push_cast; ring⟩

theorem natPow_mem_zq {q : ℕ} (hq : q ≠ 0) (k : ℕ) : (q : ℂ) ^ k ∈ zq q hq :=
  ⟨(q : ℤ) ^ k, 0, by push_cast; simp⟩

theorem inv_natPow_mem_zq {q : ℕ} (hq : q ≠ 0) (k : ℕ) : ((q : ℂ) ^ k)⁻¹ ∈ zq q hq :=
  ⟨1, k, by simp⟩

theorem single_mem {G : Type} (S : Subring ℂ) (x : G) {c : ℂ} (hc : c ∈ S) (g : G) : Finsupp.single x c g ∈ S := by
  classical
  rw [Finsupp.single_apply]
  split_ifs
  · exact hc
  · exact S.zero_mem

theorem conv_mem {G : Type} [Group G] (S : Subring ℂ) (F f : G →₀ ℂ) (hF : ∀ g, F g ∈ S) (hf : ∀ g, f g ∈ S) (x : G) :
    OpPoly.conv F f x ∈ S := by
  classical
  simp only [OpPoly.conv, Finsupp.sum, Finsupp.finsetSum_apply]
  refine Subring.sum_mem _ fun g _ => Subring.sum_mem _ fun h _ => ?_
  exact single_mem S _ (S.mul_mem (hF g) (hf h)) x

theorem opOf_zero_vec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (F : G →₀ ℂ) :
    opOf ρ F 0 = 0 := by
  simp [opOf]

theorem exists_poly_op (S : Subring ℂ) {G I : Type} [Group G] (f : I → G →₀ ℂ) (hf : ∀ i g, f i g ∈ S)
    (P : MvPolynomial I ℤ) : ∃ F : G →₀ ℂ, (∀ g, F g ∈ S) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (z : I → ℂ) (v : V),
        (∀ i, opOf ρ (f i) v = z i • v) → opOf ρ F v = MvPolynomial.aeval z P • v := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Finsupp.single 1 (a : ℂ), single_mem S 1 (intCast_mem S a), fun V _ _ ρ z v _ => ?_⟩
    simp [opOf]
  | add p q hp hq =>
    obtain ⟨F₁, h₁, e₁⟩ := hp
    obtain ⟨F₂, h₂, e₂⟩ := hq
    refine ⟨F₁ + F₂, fun g => ?_, fun V _ _ ρ z v hz => ?_⟩
    · rw [Finsupp.add_apply]
      exact S.add_mem (h₁ g) (h₂ g)
    · rw [opOf_add, e₁ V ρ z v hz, e₂ V ρ z v hz, map_add (f := _), add_smul]
  | mul_X p i hp =>
    obtain ⟨F, hF, e⟩ := hp
    refine ⟨OpPoly.conv F (f i), conv_mem S F (f i) hF (hf i), fun V _ _ ρ z v hz => ?_⟩
    rw [opOf_conv, hz i, opOf_smul, e V ρ z v hz, map_mul, MvPolynomial.aeval_X, smul_smul, mul_comm]

theorem exists_finsupp_heckeVec (S : Subring ℂ) {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (hS : ∀ g, h g ∈ S) :
    ∃ F : G →₀ ℂ, (∀ g, F g ∈ S) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
      opOf ρ F x = heckeVec ρ K h x := by
  classical
  let s := (Formalism.UG.P.finite_support_cosets hK hh.2).toFinset
  refine ⟨∑ c ∈ s, Finsupp.single c.out (h c.out), fun g => ?_, fun V _ _ ρ x => ?_⟩
  · rw [Finsupp.finsetSum_apply]
    exact Subring.sum_mem _ fun c _ => single_mem S _ (hS _) g
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← opHom_apply ρ x, map_sum, heckeVec, finsum_eq_sum_of_support_subset (s := s)]
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [opHom_apply, opOf_single]
      · intro c hc
        simp only [s, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact fun h0 => hc (by simp [h0])

end GlobalTheory.Cong.SphOpsProof

namespace GlobalTheory.Cong.SphOpsProof

open GlobalTheory.LFun Formalism.UG GlobalTheory.Cong.OpPoly

theorem normV_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : normV w = qV E w := by
  rw [normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem inv_center_act {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V)
    (ϖ : (w.adicCompletion E)ˣ) (hp : IsUnifV E w (ϖ : w.adicCompletion E)) {B : Multiset ℂˣ} {v : V}
    (hv : IsSatVecGL w ρ v B) :
    satEig (qV E w) a B a ≠ 0 ∧ ρ (ConjPlace.dGL a ϖ a)⁻¹ v = (satEig (qV E w) a B a)⁻¹ • v := by
  have h1 := ConjPlace.apply_heckeVec_shift (Tj_mem_hecke (n := a) hp a).1 hv.2.1 (ConjPlace.dGL a ϖ a)
  rw [funext (ConjPlace.Tj_shift_self _ ϖ), ExSatGL.heckeVec_Tj_zero ρ _ hv.2.1, hv.2.2.2 _ hp a le_rfl] at h1
  have h2 : v = satEig (qV E w) a B a • ρ (ConjPlace.dGL a ϖ a)⁻¹ v := by
    rw [← map_smul, ← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h0 : satEig (qV E w) a B a ≠ 0 := fun e => hv.1 (by rw [h2, e, zero_smul])
  refine ⟨h0, ?_⟩
  conv_rhs => rw [h2]
  rw [smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem esymm_inv_algSat {q : ℕ} (hq : q ≠ 0) {a : ℕ} {B : Multiset ℂˣ} (hB : B.card = a) {j : ℕ} (hj : j ≤ a)
    (hne : satEig q a B a ≠ 0) :
    ((UpperTheory.V.Af.algSat a q B).map (·⁻¹)).esymm j =
      (UpperTheory.V.Af.algSat a q B).esymm (a - j) * (((q : ℂ) ^ a.choose 2)⁻¹ * (satEig q a B a)⁻¹) := by
  first
  | exact @_root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat
  | exact _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat
  | (apply _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> assumption)
  | (intros; apply _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat ..)

theorem sphOps : SphOps := by
  intro E _ _ w a
  refine ⟨fun σ h => GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred h, fun n => ?_⟩
  have hq : qV E w ≠ 0 := qV_ne_zero w
  let S := zq (qV E w) hq
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  have hTS : ∀ j g, Tj ℂ a (Ov E w) (ϖ : w.adicCompletion E) j g ∈ S := fun j g => by
    classical
    rw [ConjPlace.Tj_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  choose T hT hTop using fun j =>
    exists_finsupp_heckeVec S (Final.GLintComm E w a) (Tj_mem_hecke (n := a) hp j) (hTS j)
  let fP : ℕ → GL (Fin a) (w.adicCompletion E) →₀ ℂ := fun j =>
    OpPoly.conv (Finsupp.single 1 ((qV E w : ℂ) ^ j.choose 2)) (T j)
  have hfP : ∀ j g, fP j g ∈ S := fun j => conv_mem S _ _ (single_mem S 1 (natPow_mem_zq hq _)) (hT j)
  have actP : ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), HasSatGL w σ.ρ B →
      ∀ v ∈ fixed σ.ρ (KGL w (n := a)), ∀ j ≤ a, opOf σ.ρ (fP j) v = (UpperTheory.V.Af.algSat a (qV E w) B).esymm j • v := by
    intro σ B hB v hv j hj
    by_cases h0 : v = 0
    · subst h0; rw [opOf_zero_vec, smul_zero]
    rw [opOf_conv, hTop j σ.V σ.ρ v, (hB.2 v hv h0).2.2.2 _ hp j hj, opOf_single, map_one, Module.End.one_apply,
      smul_smul, UpperTheory.V.Af.satEig_eq_algSat hq, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hq)), one_mul]
  let fN : Fin (a + 1) → GL (Fin a) (w.adicCompletion E) →₀ ℂ := fun j =>
    OpPoly.conv (Finsupp.single (ConjPlace.dGL a ϖ a)⁻¹ ((qV E w : ℂ) ^ a.choose 2)⁻¹) (fP (a - j))
  have hfN : ∀ j g, fN j g ∈ S := fun j => conv_mem S _ _ (single_mem S _ (inv_natPow_mem_zq hq _)) (hfP _)
  have actN : ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), HasSatGL w σ.ρ B →
      ∀ v ∈ fixed σ.ρ (KGL w (n := a)), ∀ j : Fin (a + 1),
        opOf σ.ρ (fN j) v = ((UpperTheory.V.Af.algSat a (qV E w) B).map (·⁻¹)).esymm j • v := by
    intro σ B hB v hv j
    by_cases h0 : v = 0
    · subst h0; rw [opOf_zero_vec, smul_zero]
    obtain ⟨hne, hinv⟩ := inv_center_act σ.ρ ϖ hp (hB.2 v hv h0)
    rw [opOf_conv, actP σ B hB v hv _ (Nat.sub_le _ _), opOf_smul, opOf_single, hinv, smul_smul, smul_smul,
      esymm_inv_algSat hq hB.card (Nat.lt_succ_iff.1 j.2) hne, mul_assoc]
  have hcard : ∀ B : Multiset ℂˣ, B.card = a → (UpperTheory.V.Af.algSat a (qV E w) B).card = a := fun B h => by
    simp [UpperTheory.V.Af.algSat, h]
  have hfin : ∀ F : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g, F g ∈ S) →
      ∀ g, ∃ (m : ℤ) (e : ℕ), F g = (m : ℂ) / ((normV w : ℕ) : ℂ) ^ e := by
    intro F hF g
    obtain ⟨m, e, he⟩ := hF g
    exact ⟨m, e, by rw [normV_eq]; exact he⟩
  by_cases hn : n = 0
  · subst hn
    refine ⟨Finsupp.single 1 (a : ℂ), hfin _ (single_mem S 1 (natCast_mem S a)), fun σ B hB v hv => ?_⟩
    rw [opOf_single, map_one, Module.End.one_apply, normV_eq]
    simp [hcard B hB.card]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hm : 1 ≤ m := by omega
    obtain ⟨P, hP⟩ := GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq a m hm
    obtain ⟨F, hF, hFa⟩ := exists_poly_op S (fun j : Fin (a + 1) => fP j) (fun j => hfP j) P
    refine ⟨F, hfin F hF, fun σ B hB v hv => ?_⟩
    rw [hFa σ.V σ.ρ (fun j => (UpperTheory.V.Af.algSat a (qV E w) B).esymm j) v
      (fun j => actP σ B hB v hv j (Nat.lt_succ_iff.1 j.2)), hP _ (hcard B hB.card), normV_eq]
    simp only [zpow_natCast]
  · have hm : 1 ≤ m := by omega
    obtain ⟨P, hP⟩ := GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq a m hm
    obtain ⟨F, hF, hFa⟩ := exists_poly_op S fN hfN P
    refine ⟨F, hfin F hF, fun σ B hB v hv => ?_⟩
    rw [hFa σ.V σ.ρ (fun j => ((UpperTheory.V.Af.algSat a (qV E w) B).map (·⁻¹)).esymm j) v (actN σ B hB v hv),
      hP _ (by rw [Multiset.card_map]; exact hcard B hB.card), normV_eq, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.Cong.SphOpsProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsCommonNaturalRepresentation
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem lowCount_eq_smallHodgeTateJumpCountOverLetter {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} (W : Wach P K LL)
    [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : Lat K LL) (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (η : ℕ) :
    TruncatedSeriesCountingBounds.lowCount W T a η = lowCount W T a η := by
  unfold TruncatedSeriesCountingBounds.lowCount lowCount
  congr 1

theorem recS_wordBase_natural : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∃ (ε : ℤˣ) (g : ZMod (RecS.nLet i w hw) → D.R.GG), IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ RecS.WordBase L HW i r ρ π w hw Cx hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i r ρ π w hw Cx hG hR h7 hF hJ hP h2 hq hd
  obtain ⟨ε, κ, hin⟩ := GlobalTheory.T.hodgeTateJumps_coefExt_of_roomy_adm7 L C₀ i r ρ π w hw Cx hR h7 hF hJ hP
  let C : Enl D i w hw := ⟨Cx.LL, Cx.inc⟩
  obtain ⟨g, hg, hwb⟩ := GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit L C₀ HW i w hw C hG r ρ π ε κ hR h7 h2 hq hd hin
  refine ⟨ε, g, hg, ?_⟩
  have hsm := GlobalTheory.HTW.Rec.recWord_small_pos L C₀ (liftIdx D i) ε g _ hR hg
  obtain ⟨hdeg, hloc, hnum⟩ := hwb
  refine
    { unram := hloc.unram
      deg := hdeg
      split := hloc.split
      t1 := fun T h => ?_
      t2 := fun T h => ?_
      t2win := fun T h => ?_
      num := hnum
      small := hsm }
  · obtain ⟨h1, h2, h3⟩ := hloc.t1 T h
    exact ⟨h1, h2, h3⟩
  · obtain ⟨⟨h1, _, _⟩, h4⟩ := hloc.t2 T h
    refine ⟨h1, fun ft a => ?_⟩
    rw [lowCount_eq_smallHodgeTateJumpCountOverLetter]
    exact h4 ft a
  · obtain ⟨⟨_, h2, h3⟩, _⟩ := hloc.t2 T h
    exact ⟨h2, h3⟩

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiCpl1Stab
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.StabLaw

section
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem rhoS_one (i : ℕ) (P : rowSG Pr sel mu) : rhoS Ch sel mu i P 1 = 1 := by
  unfold rhoS LocE.unitV
  simp [TopStep.reduction_one₂]
end

theorem xiCpl1_stab : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → ∀ (u : Pr.Word) (al : L.β m2) (b : L.β (m2 + 1)) (p : ChPt (R := R) sel mu u m2) (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (a : FrmG (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b)), Y ∈ ybSet sel mu cst p'.deco.1.N → a • p' = p' → (fun v => a.1.1 v) '' Y = Y → ∀ x, XiCpl1 Ch sel mu cst L m2 al p p' Y (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst m2 P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((L.levG (m2 + 1) b).chr a.2.1 * (L.levQ (m2 + 1) b).chr a.2.2 : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u al b p p' Y a hp1 hfix hY x
  have hd := (TopStep.tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2
  obtain ⟨κ', a', hκ', ha', ea'⟩ := TopLaw.exists_pass hd a p'
  have hp2 : (fun v => a.1.1 v) '' Y ∈ ybSet sel mu cst (a • p').deco.1.N := (ybSet_gmap sel mu cst _ a.1.1 Y).2 hp1
  have ha : ∀ P, TopLaw.LevAt (L.levG m2 al) (L.levQ m2 al) P ((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P) ((fun _ => 1 : rowSG Pr sel mu → X.Kˣ) P) := by
    intro P
    refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
    · refine ⟨by rw [Pi.one_apply, map_one]; exact one_mem _, ?_⟩
      exact (map_one _).symm.trans (congrArg _ (Subtype.ext (map_one _).symm))
    · exact ⟨one_mem _, (map_one _).symm⟩
  have hκ : ∀ P, frsF sel mu ((1 : FrmG (L.levG m2 al) (L.levQ m2 al)) • p) P =
      (1 : UF X.E (R.N m2)).1 * (frsF sel mu p P * (((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P)⁻¹).1) := fun P => by
    rw [one_smul]; simp
  have law := CoupledLaw.xiCpl1_law (G := G) (q := (1 : FrmG (L.levG m2 al) (L.levQ m2 al)) • p) hX hPr hL hp1 hp2 hκ hκ' ha ha' x
    (TopLaw.phiT_act _ _ _ _ _ _ _)
  rw [one_smul, hfix, hY] at law
  rw [hfix] at hκ'
  have hdet : ∀ P, (LinearEquiv.det a.1.1 : X.Eˣ) = LinearEquiv.det (κ' P).1 := fun P => by
    have h := congrArg LinearEquiv.det (hκ' P)
    rw [map_mul, map_mul, InvMemClass.coe_inv, map_inv] at h
    rw [mul_left_comm] at h
    exact mul_inv_eq_one.mp (mul_left_cancel (h.symm.trans (mul_one _).symm))
  have hprod : ∀ P, muAt Ch sel mu cst m2 P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) =
      rhoS Ch sel mu m2 P ((LinearEquiv.det ((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P).1 : X.Eˣ) : X.E) *
        rhoT Ch sel mu m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E) := fun P => by
    rw [hdet P, MatLaw.muAt_det, Pi.inv_apply, TopLaw.rhoT_inv, Pi.one_apply, OneMemClass.coe_one, map_one,
      Units.val_one, rhoS_one, one_mul]
  have e : x ∘ₗ ((1 : UF X.E (R.N m2)) : Sp X.E (R.N m2) ≃ₗ[X.E] Sp X.E (R.N m2)).symm.toLinearMap = x :=
    LinearMap.ext fun v => rfl
  rw [e, Finset.prod_const_one, inv_one, inv_one, mul_one, ea'] at law
  rw [Finset.prod_congr rfl fun P _ => hprod P]
  exact law

end GlobalTheory.StabLaw
end
end

