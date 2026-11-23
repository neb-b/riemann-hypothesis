module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsDictionaryAtEmbeddingOverRealPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.JumpDictRec

open GlobalTheory.JumpDictionaryFoundation

theorem main : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D →
    GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool),
    (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ,
      (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i),
        D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧
        (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) =
          {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  intro D hW hB hG hC i τ ρ b hτ
  have hs := shift_embOver D ρ b
  refine ⟨shift D (embOver D ρ b), ?_, fun w hw => ?_⟩
  · apply Multiset.map_injective (f := fun q : ℚ => (q : ℂ)) Rat.cast_injective
    rw [Multiset.map_map, Multiset.map_map]
    have e0 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
    rw [hτ] at e0
    have e1 : (D.naut.locAutHodgeTateWeightsLevelZero i τ).map ((fun q : ℚ => (q : ℂ)) ∘ fun n : ℤ => (n : ℚ)) =
        (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℂ)) :=
      Multiset.map_congr rfl fun n _ => by simp
    rw [e1, e0]
    cases b
    · rw [(hW i ρ).1, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
    · rw [(hW i ρ).2, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
  · have ht : 1 ≤ D.R.t := by
      obtain ⟨u, v, -, hv, -⟩ := exists_halves D.R
      omega
    have hz : ∀ φ, ∃ z : ℤ, (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) φ).map
        (· + (blockExp D 1 : ℂ)) = {(z : ℂ)} := by
      intro φ
      obtain ⟨ρ', b', rfl⟩ := exists_embOver D φ
      obtain ⟨a, ha⟩ := firstJump_int D i ρ' b'
      refine ⟨-a, ?_⟩
      rw [inf_block D hB, ha]
      push_cast
      simp
    choose z hz using hz
    obtain ⟨r, hrc, hrf, hrd, hrj⟩ := hG i _ _ z hz
    have hr : r = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1) := by
      have h := eq_of_frob D.nd hC i
        (a := fun g => ((r g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)
        (b := fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i))
        ((continuous_apply 0).comp ((continuous_apply 0).comp hrc))
        ((continuous_iotaOQ D i w hw).comp (D.nd.chi_cont i 1)) fun v hv B σ hB' hσ => by
          have e1 := hrf v hv.2.1 (D.naut.chi_mu i v hv).1 B σ hB' hσ
          rw [chi_frob D i 1 le_rfl ht v hv B σ hB' hσ, Multiset.singleton_inj] at e1
          exact ((D.naut.iotaQC i).injective e1).symm
      ext g a c
      obtain rfl : a = 0 := Subsingleton.elim _ _
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine (congrFun h g).trans ?_
      rw [← chiGL_apply D i 1 g 0 0]
      rfl
    subst hr
    refine ⟨hrd w hw, ?_⟩
    have hq : firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1) = ((-z (embOver D ρ b) : ℤ) : ℚ) := by
      have e := (inf_block D hB i 1 ρ b).symm.trans (hz _)
      rw [Multiset.singleton_inj] at e
      have e' : -(firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1)) = (z (embOver D ρ b) : ℚ) := by exact_mod_cast e
      rw [Int.cast_neg, ← e', neg_neg]
    rw [hrj, hτ, Multiset.map_singleton, ← hq, hs]
    congr 1
    cases b
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring

end GlobalTheory.JumpDictRec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeAdjoinCompatibleRootsOfFiniteKummerTower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KinfFin

theorem seq_add_pow {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) (m k : ℕ) :
    ϖ.seq (m + k) ^ l ^ k = ϖ.seq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, ϖ.seq_succ, ih]

theorem adjoin_mono {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) :
    Monotone fun n => IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine IntermediateField.adjoin_simple_le_iff.2 ?_
  have : ϖ.seq m ^ e = (ϖ.seq (m + k) ^ e) ^ l ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, seq_add_pow]
  rw [this]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _

theorem Kinf_eq_iSup {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) :
    ϖ.Kinf = ⨆ n, IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  rw [PiSys.Kinf, ← IntermediateField.biSup_adjoin_simple, iSup_range]

theorem exists_mem_of_mem_Kinf {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) {x : Om l}
    (hx : x ∈ ϖ.Kinf) : ∃ n, x ∈ IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  rw [Kinf_eq_iSup, ← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed (adjoin_mono ϖ).directed_le, Set.mem_iUnion] at hx
  exact hx

theorem main : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (ϖ : PiSys l e) (F : IntermediateField ℚ_[l] (Om l)),
    FiniteDimensional ℚ_[l] F → F ≤ ϖ.Kinf → ∃ n : ℕ, F ≤ IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  intro l _ e ϖ F hF hle
  classical
  let b := Module.finBasis ℚ_[l] F
  choose N hN using fun i => exists_mem_of_mem_Kinf ϖ (hle (b i).2)
  refine ⟨Finset.univ.sup N, fun x hx => ?_⟩
  change ((⟨x, hx⟩ : F) : Om l) ∈ _
  rw [← b.sum_repr ⟨x, hx⟩, IntermediateField.coe_sum]
  refine sum_mem fun i _ => ?_
  rw [IntermediateField.coe_smul]
  refine IntermediateField.smul_mem _ ?_
  exact adjoin_mono ϖ (Finset.le_sup (f := N) (Finset.mem_univ i)) (hN i)

end GlobalTheory.KinfFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitQuotientPrimePowEqExponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.LenUnitPow

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]


variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem _root_.GlobalTheory.LenUnitPow.natCast_ne_zero : (l : O) ≠ 0 := by
  intro h
  have hker : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := by
    refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
    intro hbot
    have hl : ((l : ℤ_[l])) ∈ RingHom.ker (algebraMap ℤ_[l] O) := by
      rw [RingHom.mem_ker, map_natCast]; exact h
    rw [hbot, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  have hbot : (⊥ : Ideal O).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) (⊥ : Ideal O) ?_
    change (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal
    rwa [← RingHom.ker_eq_comap_bot]
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm


variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem _root_.GlobalTheory.LenUnitPow.natCast_not_isUnit : ¬ IsUnit (l : O) := by
  intro h
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal O)
  have hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O) := by
    rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hl
  exact hl h

end GlobalTheory.LenUnitPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramifiedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_Dcris_eq_DdR_crystalline_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  first | exact @GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR | exact GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR | (intros; apply GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulLeft
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.SandArb

theorem map_mulLeft {O R M : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M]
    (a : R) (z : R ⊗[O] M) :
    TensorProduct.map (LinearMap.mulLeft O a) LinearMap.id z = a • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add (f := _), smul_add, hx, hy]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) {s : ℕ} (hs : W.s = s)
    (hp : PD.p.Prime) (hL : LevLaws W) (hI : IoLaws E)


set_option maxHeartbeats 1000000 in
theorem of_layers {Zl : Type} [CommRing Zl] (zl : PowerSeries Zl →+* LetA O n) (h1 : IsCrys PD W.one.ρ)
    (hP : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (w : RA) (c : RW) (hc : c = inclR w)
    (hS : GlobalTheory.HWL.Sand (latOf E hs hp hL hI zl h1 hP) T w) :
    (∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x)) ∧
      ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)} := by
  subst hc
  have hN : nOf W T = W.N T := nOf_crys W hT
  have h1' : ∀ x ∈ nOf W T, ∃ y : TW RA T, TWincl inclR T y = inclR w • E.jD T x := hS.1
  have h2' : ∀ t : ↥T.L.T, inclR w • ((1 : RW) ⊗ₜ[O] t : TW RW T) ∈
      Submodule.span O {z : TW RW T | ∃ (a : RA), ∃ y ∈ nOf W T, z = inclR a • E.jD T y} := hS.2
  rw [hN] at h1' h2'
  refine ⟨fun x hx => ?_, fun t => ?_⟩
  · rw [map_mulLeft]; exact h1' x hx
  · have := h2' t
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
    simp only [map_mulLeft]
    exact this

end Generic

section
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (hL : Laws H F h)


set_option maxHeartbeats 400000 in
theorem sand_layers (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    ∃ m : ℕ, GlobalTheory.HWL.Sand (LatL H F h hL) T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) :=
  apply_layers H F h hL
    (fun _ _ _ _ Mo => ∃ m : ℕ, GlobalTheory.HWL.Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL))
    (fun Γ R I hI E Mo => GlobalTheory.HWL.SandProof.sandwich l P AI K s LL h Γ R I hI E Mo T hT)

theorem incl_pow (a : RA LL) (w : Ainf l) (ha : a = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) (m : ℕ) :
    inclR LL a ^ m = inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w ^ m)) := by
  rw [ha, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]

end


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem sandwich : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∃ m : ℕ, (∀ x ∈ W.N T, ∃ y : TW (RA LL) T, TWincl (inclR LL) T y = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io W.X) ^ m)) LinearMap.id (E.jD T x)) ∧ ∀ t : ↥T.L.T, ((inclR LL (E.io W.X) ^ m) ⊗ₜ[↥(OL LL)] t : TW (RW LL) T) ∈ Submodule.span ↥(OL LL) {z : TW (RW LL) T | ∃ a : RA LL, ∃ y ∈ W.N T, z = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL a)) LinearMap.id (E.jD T y)} := by
  intro D HW F l _ K s LL h
  have hL : Laws (HW l) (F l) h := GlobalTheory.T.wach_functor_three_layer_properties_every_place D HW F l K s LL h
  have hX := (GlobalTheory.T.wachInclusion_X_Q_frobenius D HW F l K s LL h).1
  refine fun T hT => (sand_layers (HW l) (F l) h hL T hT).imp fun m hm => ?_
  exact of_layers ((F l).E K s LL h).tie ((HW l).W_s K s LL h) (p_prime (D.loc l) K) hL.lev hL.io _ hL.one
    ((HW l).W_proj K s LL h) T hT _ _ (incl_pow _ _ hX m) hm

end GlobalTheory.NL.SandArb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemKummerTowerUnramifiedOfCoversOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem theta_algebraMap_inj {z z' : ℤ_[l]}
    (h : Per.θ l (algebraMap ℤ_[l] (Ainf l) z) = Per.θ l (algebraMap ℤ_[l] (Ainf l) z')) : z = z' := by
  have h1 := GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z
  have h2 := GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z'
  have h3 : (algebraMap ℚ_[l] ℂ_[l]) (z : ℚ_[l]) = (algebraMap ℚ_[l] ℂ_[l]) (z' : ℚ_[l]) := by
    rw [← h1, ← h2]
    exact congrArg Subtype.val h
  exact PadicInt.ext ((algebraMap ℚ_[l] ℂ_[l]).injective h3)

theorem one_tmul_injective (LL : FinExt l) {y y' : Ainf l}
    (h : (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] y = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] y') : y = y' := by
  have hA : Function.Injective (algebraMap ℤ_[l] (Ainf l)) := fun z z' hz =>
    theta_algebraMap_inj (congrArg (Per.θ l) hz)
  have : Module.IsTorsionFree ℤ_[l] (Ainf l) := Module.isTorsionFree_iff_algebraMap_injective.2 hA
  have hO : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := fun z z' hz => by
    refine theta_algebraMap_inj ?_
    rw [← intToOC_algebraMap, ← intToOC_algebraMap, hz]
  exact Algebra.TensorProduct.includeRight_injective (R := ℤ_[l]) (A := ↥(OL LL)) (B := Ainf l) hO h

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem ratio_pow {e : ℕ} (ϖ : PiSys l e) (g : GQ l) (n m : ℕ) : ϖ.ratio g (n + m) ^ l ^ m = ϖ.ratio g n := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, ← add_assoc, ϖ.ratio_succ, ih]

theorem seq_fixed {e : ℕ} [NeZero e] (ϖ : PiSys l e) {g : GQ l} (hg : ϖ.kummer g = 1) (n : ℕ) :
    g (ϖ.seq n) = ϖ.seq n := by
  have hd : ∀ j, ((l : ℕ) : OC l) ∣ ϖ.ratio g j - 1 := fun j => by
    have h1 := ϖ.coeff_kummer g j
    rw [hg, map_one] at h1
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_one, ← h1]
  have hr : ϖ.ratio g n = 1 := by
    rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {((l : ℕ) : OC l)})]
    intro m
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rcases m with _ | m
    · simp
    · have := dvd_sub_pow_of_dvd_sub (hd (n + m)) m
      rwa [ratio_pow, one_pow] at this
  have h2 := congrArg Subtype.val hr
  rw [PiSys.coe_ratio, OneMemClass.coe_one, ← map_one (algebraMap (Om l) ℂ_[l])] at h2
  exact (div_eq_one_iff_eq (ϖ.seq_ne_zero n)).1 ((algebraMap (Om l) ℂ_[l]).injective h2)

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

variable {l : ℕ} [Fact l.Prime]

theorem unr_fixed (a : ℕ) [NeZero a] {g : GQ l} (hg : ∀ w, Per.σA g (wA l a w) = wA l a w) {x : Om l}
    (hx : x ^ l ^ a = x) : g x = x := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h1 := congrArg (fun y => ((Per.θ l y : OC l) : ℂ_[l])) (hg (WittVector.teichmuller l z))
  simp only [GlobalTheory.RingBasics.θ_σA, wA_teich, WittVector.fontaineTheta_teichmuller] at h1
  have h2 : Per.σC g (ω : ℂ_[l]) = (ω : ℂ_[l]) := by
    rw [← GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
    exact (GlobalTheory.RingIface.sigO_coe l g _).symm.trans h1
  rw [GlobalTheory.RingBasics.σC_coe] at h2
  have hω' : g ω = ω := UniformSpace.Completion.coe_injective _ h2
  rcases eq_or_ne x 0 with rfl | h0
  · exact map_zero g
  have h3 := one_lt_pow_l l a
  have h4 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h3.le, hx, one_mul])
  have : NeZero (l ^ a - 1) := ⟨by omega⟩
  obtain ⟨i, -, rfl⟩ := hω.eq_pow_of_pow_eq_one h4
  rw [map_pow, hω']

end GlobalTheory.CoverOne

namespace GlobalTheory.CoverOne

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l), Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) → k ∈ ϖ.GfieldInf a := by
  intro l _ a e _ _ ϖ LL _ _ k hc
  have hfix : ∀ f, galOA ↥(OL LL) k (ϖ.iTot (thetaW a LL) ↥LL.1 f) = ϖ.iTot (thetaW a LL) ↥LL.1 f :=
    fun f => hc f f fun τ => by rw [map_one]; rfl
  have hev : ∀ x, Per.σA k (ϖ.ev a x) = ϖ.ev a x := fun x => by
    have h := hfix (toAc (thetaW a LL) ↥LL.1 x)
    rw [PiSys.iTot_toAc, galOA_tmul] at h
    exact one_tmul_injective LL h
  have hteich : Per.σA k ϖ.teich = ϖ.teich := by simpa using hev X
  have h0 : ϖ.teich ≠ 0 := fun h => ϖ.flat_ne_zero (by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simpa [PiSys.teich] using this)
  have hkum : ϖ.kummer k = 1 := by
    rw [PiSys.gal_teich, PiSys.mu, add_sub_cancel] at hteich
    have h1 := mul_right_cancel₀ h0 (hteich.trans (one_mul _).symm)
    have h2 := congrArg (fun w : Ainf l => w.coeff 0) h1
    simpa using h2
  have hseq := seq_fixed ϖ hkum
  have hw : ∀ w, Per.σA k (wA l a w) = wA l a w := fun w => by simpa using hev (C w)
  have hz : ∀ x, k x = x → x ∈ IntermediateField.fixedField (Subgroup.zpowers k) := fun x hx => by
    rintro ⟨_, m, rfl⟩
    exact MulAction.mem_fixedBy_zpow (α := Om l) (g := k) (a := x) hx m
  rw [PiSys.GfieldInf, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact IntermediateField.adjoin_le_iff.2 fun x hx => hz x (unr_fixed a hw hx)
  · exact IntermediateField.adjoin_le_iff.2 fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact hz _ (hseq 0)
  · exact IntermediateField.adjoin_le_iff.2 fun x ⟨n, hn⟩ => hn ▸ hz _ (hseq n)

end GlobalTheory.CoverOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPowSmulLatticeOfCoordDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem mem_pow_smul_of_coord_dvd : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) → ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T x k h
  haveI : Module.Free O ↥T.L.T := T.L.free
  let b := Module.Free.chooseBasis O ↥T.L.T
  let f := Module.Free.chooseBasis ℤ_[l] O
  have hφ : ∀ i j, (l : ℤ_[l]) ^ k ∣ f.repr (b.repr x i) j := by
    intro i j
    let φ : ↥T.L.T →+ ℤ_[l] := ((f.coord j).toAddMonoidHom).comp (b.coord i).toAddMonoidHom
    have := h φ (by
      intro z t
      show f.coord j (b.coord i (algebraMap ℤ_[l] O z • t)) = z * f.coord j (b.coord i t)
      rw [LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
    simpa [φ] using this
  choose w hw using hφ
  let c : _ → O := fun i => ∑ j ∈ (f.repr (b.repr x i)).support, w i j • f j
  let y : ↥T.L.T := ∑ i ∈ (b.repr x).support, c i • b i
  have hc : ∀ i, (l : O) ^ k * c i = b.repr x i := by
    intro i
    have hl : (l : O) ^ k = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ k) := by simp
    conv_rhs => rw [← f.linearCombination_repr (b.repr x i)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hl, ← Algebra.smul_def, smul_smul, hw i j]
  have hx : x = (l : O) ^ k • y := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hc i]
  refine ⟨(y : T.V), y.2, ?_⟩
  rw [hx]
  rfl

end GlobalTheory.InertiaEigenvalues
end

