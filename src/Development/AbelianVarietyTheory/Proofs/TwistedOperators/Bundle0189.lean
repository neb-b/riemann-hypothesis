module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CxRootsInjective
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem cxRoots_root (i : Fin r) : eval₂ τ.1 (cxRoots τ.1 P i) P.1 = 0 := by
  rw [← eval_map, cxRoots_spec, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem cxRoots_injective : Function.Injective (cxRoots τ.1 P) := by
  have hs : (P.1.map τ.1).Separable := (PerfectField.separable_of_irreducible P.2.2.1).map
  have hn := nodup_roots hs
  rw [cxRoots_spec, ← Finset.prod_map_val,
    show Multiset.map (fun i => X - C (cxRoots τ.1 P i)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Finset.univ.val.map (cxRoots τ.1 P)) by rw [Multiset.map_map]; rfl,
    roots_multiset_prod_X_sub_C] at hn
  exact fun i j h => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).1 hn i (by simp) j (by simp) h

theorem finrank_Fld : Module.finrank E (Fld P) = r :=
  ((AdjoinRoot.powerBasis P.2.2.1.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim _)).trans P.2.2.2.1

def psiL (i : Fin r) : Fld P →+* ℂ := AdjoinRoot.lift τ.1 (cxRoots τ.1 P i) (cxRoots_root P τ i)

@[simp] theorem psiL_algebraMap (i : Fin r) (e : E) : psiL P τ i (algebraMap E (Fld P) e) = τ.1 e :=
  AdjoinRoot.lift_of _

@[simp] theorem psiL_alpha (i : Fin r) : psiL P τ i (alpha P) = cxRoots τ.1 P i := AdjoinRoot.lift_root _

theorem psiL_algebraMap_F (i : Fin r) (a : F) : psiL P τ i (algebraMap F (Fld P) a) = w.embedding a := by
  rw [IsScalarTower.algebraMap_apply F E (Fld P), psiL_algebraMap]
  exact RingHom.congr_fun τ.2 a

def Psi (i : Fin r) : w.Completion ⊗[F] Fld P →+* ℂ :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  (Algebra.TensorProduct.productMap
    ({ InfinitePlace.Completion.extensionEmbedding w with
        commutes' := fun a => by
          change InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion a) = w.embedding a
          rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
            Algebra.algebraMap_self_apply, InfinitePlace.Completion.extensionEmbedding_coe,
            ← WithAbs.equiv_symm_apply, RingEquiv.apply_symm_apply] } :
      w.Completion →ₐ[F] ℂ)
    ({ psiL P τ i with commutes' := fun a => psiL_algebraMap_F P τ i a } : Fld P →ₐ[F] ℂ)).toRingHom

@[simp] theorem Psi_tmul (i : Fin r) (a : w.Completion) (y : Fld P) :
    Psi P τ i (a ⊗ₜ[F] y) = InfinitePlace.Completion.extensionEmbedding w a * psiL P τ i y := rfl

def PsiAll : w.Completion ⊗[F] Fld P →+* (Fin r → ℂ) := Pi.ringHom (Psi P τ)

@[simp] theorem PsiAll_apply (y : w.Completion ⊗[F] Fld P) (i : Fin r) : PsiAll P τ y i = Psi P τ i y := rfl

end GlobalTheory.TrEll.RealTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.LevelOff

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ind_tmul_mul (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E) :
    (GlobalTheory.AdeleIdem.ind Sb ⊗ₜ[F] (1 : E)) * z =
      ∑ v ∈ Sb, (GlobalTheory.AdelicU.singleFin v).rTensor E
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      LinearMap.rTensor_tmul]
    rw [← TensorProduct.sum_tmul]
    congr 1
    refine GlobalTheory.AdelicU.af_ext fun u => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum]
    by_cases hu : u ∈ Sb
    · rw [Finset.sum_eq_single u (fun v _ hv => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hv) _)
        (fun h => absurd hu h), GlobalTheory.AdelicU.evalV_singleFin_self]
      show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _
      rw [if_pos hu, one_mul]
    · rw [Finset.sum_eq_zero (fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne (fun e : u = v => hu (e ▸ hv)) _)]
      show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _
      rw [if_neg hu, zero_mul]
  | add x y hx hy => rw [mul_add, hx, hy, ← Finset.sum_add_distrib]; simp only [map_add (f := _)]

theorem ind_tmul_mul_eq_zero (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E)
    (h : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z = 0) :
    (GlobalTheory.AdeleIdem.ind Sb ⊗ₜ[F] (1 : E)) * z = 0 := by
  rw [ind_tmul_mul]
  exact Finset.sum_eq_zero fun v hv => by rw [h v hv, map_zero]

theorem one_sub_ind_tmul_mul (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E)
    (h : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z = 0) :
    ((1 - GlobalTheory.AdeleIdem.ind Sb) ⊗ₜ[F] (1 : E)) * z = z := by
  rw [TensorProduct.sub_tmul, sub_mul, ← Algebra.TensorProduct.one_def, one_mul, ind_tmul_mul_eq_zero Sb z h, sub_zero]

open Filter GlobalTheory.AdelicU

variable {D : D7}

theorem mem_KsphC_iff (V : HSp D) (g : GA D V) : g ∈ KsphC V ∅ ↔ g ∈ GfC V ∧ ∀ v, projV V v g ∈ Kv V v := by
  have e : g ∈ KsphC V ∅ ↔ g ∈ ((levelOff D.sp.cm.sig V.gram (frameLat V) ∅ : Subgroup _) : Set (GA D V)) := by
    rw [KsphC_eq]
  rw [e, SetLike.mem_coe, mem_levelOff, GfC_eq]
  simp

theorem eq_L0sub {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) : Λ = GlobalTheory.LevSplit.L0sub V := by
  obtain ⟨-, -, -, h01, h10⟩ := hB
  ext x
  constructor
  · intro hx
    show x ∈ L0c D V
    simpa using h10 x hx
  · intro hx
    simpa using h01 x hx

theorem finE_mem_St_iff {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) {g : GA D V} (hg : g ∈ GfC V) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ g ∈ KsphC V ∅ := by
  have hfr : Formalism.L2.DIV.IsFrame β (GlobalTheory.LevSplit.L0sub V) := eq_L0sub hB ▸ hB.1
  have e1 := GlobalTheory.LevSplit.mem_St_iff β _ hfr (Formalism.IndefR.Lev.finE V g)
  have e2 := GlobalTheory.LevSplit.ksph_iff V g
  exact e1.trans ⟨fun h => e2.2 ⟨hg, h⟩, fun h => (e2.1 h).2⟩

theorem finE_mem_St_of_mem_levG {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Lv : LevDat D.host.E ℂ V.rank}
    {g : GA D V} (hg : g ∈ levG V β Lv) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β :=
  Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hg.2)

open Filter GlobalTheory.AdelicU

variable {D : D7}

theorem evalV_finPart (v : HeightOneSpectrum (𝓞 D.host.F)) (w : AE D) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (Formalism.L2.Theta.finPart D w) =
      compFin D.host.F D.host.E v w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, _root_.map_zero, RingHom.map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), _root_.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem redFn_eq_one_of_proj {V : HSp D} (β : GL (Fin V.rank) (EAf D)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    {h : GA D V} (hS : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.St β) (h1 : ∀ v ∈ Sb, projV V v h = 1)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sb) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V h) = 1 := by
  classical
  set b : FiniteAdeleRing (𝓞 D.host.F) D.host.F := 1 - GlobalTheory.AdeleIdem.ind Sb with hbdef
  have hb : b ∈ Formalism.UG.intAd D.host.F := sub_mem (one_mem _) (GlobalTheory.AdeleIdem.ind_mem Sb)
  refine GlobalTheory.LevSplit.redFn_eq_one β PP _ hS ⟨_, GlobalTheory.AdeleIdem.one_tmul_mem hb⟩ ?_ ?_
  · refine GlobalTheory.AdeleIdem.resS_eq_zero PP ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) rfl hb ?_
    simp [hbdef, GlobalTheory.AdeleIdem.ind_apply, hPP]
  · ext i j
    set w : AE D := (Formalism.L2.Theta.mt V h - 1) i j with hw
    have e0 : ((Formalism.L2.Theta.mt V h) - 1).map (GlobalTheory.LevSplit.finSw D) = (Formalism.L2.Theta.mt V h).map (GlobalTheory.LevSplit.finSw D) - 1 := by
      rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
    have ex : ((Formalism.IndefR.Lev.finE V h).1 - 1) i j = Formalism.IndefR.Lev.swapAE D (Formalism.L2.Theta.finPart D w) := by
      rw [GlobalTheory.LevSplit.finE_val, ← e0]
      rfl
    have hz : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Formalism.L2.Theta.finPart D w) = 0 := by
      intro v hv
      rw [evalV_finPart]
      have e1 : (Formalism.L2.Theta.mt V h).map (compFin D.host.F D.host.E v) = 1 := by
        have e2 : (matHom _ D.sp.cm.sig V.gram (projV V v h)).1 = 1 := by
          rw [h1 v hv, MonoidHom.map_one, Units.val_one]
        exact e2
      have e3 : ((Formalism.L2.Theta.mt V h) - 1).map (compFin D.host.F D.host.E v) = 0 := by
        rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), e1, sub_self]
      exact congrFun (congrFun e3 i) j
    rw [Matrix.smul_apply, smul_eq_mul, ex]
    show Formalism.IndefR.Lev.swapAE D (b ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [← RingHom.map_mul]
    refine congrArg (Formalism.IndefR.Lev.swapAE D) ?_
    exact one_sub_ind_tmul_mul Sb _ hz

open GlobalTheory.AdelicU

theorem level_offS : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Lv : LevDat D.host.E ℂ V.rank) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBaseFrame V β Λ 1 → (∀ PP, PP ∈ Lv.Pg ∨ PP ∈ Lv.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sb) → SphOff (levG V β Lv : Set (GA D V)) (levChi V β Lv) Sb ∧ (∀ g ∈ GfC V, g ∈ levG V β Lv ↔ (∃ k ∈ levG V β Lv, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v) ∧ (∀ g : GA D V, {v | projV V v g ∉ Kv V v}.Finite) ∧ ∀ k ∈ levG V β Lv, ‖levChi V β Lv k‖ = 1 := by
  intro D V β Λ Lv Sb hB hPl
  have hsplit := GlobalTheory.LevSplit.lev_split V β Λ 1 Lv hB
  have hK : ∀ k ∈ levG V β Lv, ∀ v, projV V v k ∈ Kv V v := fun k hk =>
    ((mem_KsphC_iff V k).1 ((finE_mem_St_iff hB hk.1).1 (finE_mem_St_of_mem_levG hk))).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    rw [GlobalTheory.GoodPrimes.offS_iff] at hP
    obtain ⟨e, f, hpe⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 P
    have h1P : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [Nat.cast_one]
      exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    obtain ⟨h1, h2, -⟩ := hsplit.2 P e f hpe h1P fun PP hPP =>
      ⟨fun e => by subst e; exact hP (hPl _ hPP),
       fun hc => hP (by rw [← GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc]; exact hPl PP hPP)⟩
    exact ⟨e, f, hpe, h1, h2⟩
  · intro g hg
    constructor
    · intro h
      exact ⟨⟨g, h, fun _ _ => rfl⟩, fun v _ => hK g h v⟩
    · rintro ⟨⟨k, hk, heq⟩, hoff⟩
      have hxf : g * k⁻¹ ∈ GfC V := mul_mem hg (inv_mem hk.1)
      have hx1 : ∀ v ∈ Sb, projV V v (g * k⁻¹) = 1 := fun v hv => by
        rw [MonoidHom.map_mul, MonoidHom.map_inv, heq v hv, mul_inv_cancel]
      have hxK : g * k⁻¹ ∈ KsphC V ∅ := (mem_KsphC_iff V _).2 ⟨hxf, fun v => by
        by_cases hv : v ∈ Sb
        · rw [hx1 v hv]; exact one_mem _
        · rw [MonoidHom.map_mul, MonoidHom.map_inv]; exact mul_mem (hoff v hv) (inv_mem (hK k hk v))⟩
      have hxS := (finE_mem_St_iff hB hxf).2 hxK
      have hxl : g * k⁻¹ ∈ levG V β Lv := ⟨hxf, GlobalTheory.LevSplit.mem_lev_of_red _ _ β Lv _
        (GlobalTheory.LevSplit.finE_mem_UA V _) hxS fun PP hPP => redFn_eq_one_of_proj β Sb hxS hx1 (hPl PP hPP)⟩
      have e : g = g * k⁻¹ * k := by rw [inv_mul_cancel_right]
      rw [e]
      exact mul_mem hxl hk
  · intro g
    haveI := SelfDual.isLattice_frameLat V
    exact Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V) g)
  · intro k hk
    obtain ⟨n, hn, h⟩ := hsplit.1 k hk
    exact Complex.norm_eq_one_of_pow_eq_one h hn.ne'

end GlobalTheory.FinZeta.LevelOff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyHermitianIntegrallyCongruentCmExt
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.HermCongAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_sigR_of {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F))
    (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y with
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem exists_norm_eq_at {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F)) (a : E)
    (ha : σ a = -a) (ha0 : a ≠ 0) (hai : 1 ⊗ₜ[F] a ∈ intLoc F E v) (hinv : 1 ⊗ₜ[F] (2 * a)⁻¹ ∈ intLoc F E v)
    (x : intLoc F E v) (hx : sigR (Fv F v) σ x = x) (hu : IsUnit x) :
    ∃ c : intLoc F E v, c.1 * sigR (Fv F v) σ c.1 = x.1 := by
  let O := intLoc F E v
  let _ := (intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) O := finite_intLocMap v
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  let s : O →+* O := (sigR (Fv F v) σ).restrict O O fun _ => sigR_mem_intLoc σ
  have hs : ∀ y : O, s (s y) = y := fun y => Subtype.ext (sigR_sigR_of hσ v y.1)
  have hk : ∀ c, s (algebraMap (v.adicCompletionIntegers F) O c) = algebraMap (v.adicCompletionIntegers F) O c :=
    fun c => Subtype.ext (by
      change sigR (Fv F v) σ ((c : Fv F v) ⊗ₜ[F] (1 : E)) = (c : Fv F v) ⊗ₜ[F] (1 : E)
      simp [sigR])
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).map (algebraMap (v.adicCompletionIntegers F) O)
  have hI : I ≤ I.comap s := Ideal.map_le_iff_le_comap.2 fun c hc => by
    rw [Ideal.mem_comap, Ideal.mem_comap, hk]
    exact Ideal.mem_map_of_mem _ hc
  have hω : IsUnit ((⟨_, hai⟩ : O) - s ⟨_, hai⟩) := by
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) (Subtype.ext ?_)
    change (inclR (Fv F v) a - inclR (Fv F v) (σ a)) * inclR (Fv F v) (2 * a)⁻¹ = 1
    rw [← map_sub, ← map_mul, ha, sub_neg_eq_add, ← two_mul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero ha0), map_one]
  obtain ⟨c, hc⟩ := GlobalTheory.HenselianNorm.exists_norm_eq O I s hs (fun y hy => hI hy) ⟨_, hω⟩ x (Subtype.ext hx) hu
  exact ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory.HermCongAlmostAll

namespace GlobalTheory.HermCongAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IntM (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Prop :=
  ∀ i j, X i j ∈ intLoc F E v

theorem intM_mul {v : HeightOneSpectrum (𝓞 F)} {X Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hX : IntM v X) (hY : IntM v Y) : IntM v (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem intM_diagonal {v : HeightOneSpectrum (𝓞 F)} {c : Fin n → Fv F v ⊗[F] E}
    (hc : ∀ i, c i ∈ intLoc F E v) : IntM v (Matrix.diagonal c) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs
  exacts [hc i, zero_mem _]

theorem mulVec_mem {v : HeightOneSpectrum (𝓞 F)} {X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (hX : IntM v X)
    {y : Fin n → Fv F v ⊗[F] E} (hy : ∀ i, y i ∈ intLoc F E v) : ∀ i, (X *ᵥ y) i ∈ intLoc F E v := fun i => by
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => mul_mem (hX i k) (hy k)

theorem eventually_intM_JR (X : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IntM v (JR (Fv F v) X) :=
  eventually_all.2 fun i => eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (X i j)

theorem JR_mul (R : Type) [CommRing R] [Algebra F R] (X Y : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (X * Y) = JR R X * JR R Y := Matrix.map_mul

theorem JR_one (R : Type) [CommRing R] [Algebra F R] : JR (F := F) R (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem JR_diagonal (R : Type) [CommRing R] [Algebra F R] (d : Fin n → E) :
    JR (F := F) R (Matrix.diagonal d) = Matrix.diagonal fun i => inclR R (d i) :=
  Matrix.diagonal_map (map_zero _)

theorem cT_JR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (sigR R σ) (JR R X) = JR R (Formalism.UG.cT (σ : E →+* E) X) := rfl

theorem cT_diagonal {A : Type} [CommRing A] (s : A →+* A) (c : Fin n → A) :
    Formalism.UG.cT s (Matrix.diagonal c) = Matrix.diagonal fun i => s (c i) := by
  unfold Formalism.UG.cT
  rw [Matrix.diagonal_map (map_zero s), Matrix.diagonal_transpose]

end GlobalTheory.HermCongAlmostAll

namespace GlobalTheory.HermCongAlmostAll

theorem eventually_congr_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) E), IsHermND σ J → IsHermND σ J' →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ u : GL (Fin n) (Fv F v ⊗[F] E),
      Formalism.UG.cT (sigR (Fv F v) σ) u.1 * JR (Fv F v) J * u.1 = JR (Fv F v) J' ∧
      ∀ y, u.1 *ᵥ y ∈ latLoc F (stdLattice E n) v ↔ y ∈ latLoc F (stdLattice E n) v := by
  intro F E _ _ _ _ _ σ h n J J' hJ hJ'
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have diag : ∀ {G : Matrix (Fin n) (Fin n) E}, IsHermND σ G → ∃ (Q Q' : Matrix (Fin n) (Fin n) E) (d : Fin n → E),
      Q * Q' = 1 ∧ Q' * Q = 1 ∧ Formalism.UG.cT (σ : E →+* E) Q * G * Q = Matrix.diagonal d ∧
      (∀ i, σ (d i) = d i) ∧ ∀ i, d i ≠ 0 := by
    intro G hG
    obtain ⟨P, d, hP, hd, hdσ, hd0⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hσ (G := G) (fun a b => hG.1 b a)
    have hu : IsUnit (P.map (σ : E →+* E)).det := by
      rw [show (P.map (σ : E →+* E)).det = (σ : E →+* E) P.det from (RingHom.map_det _ P).symm]
      exact ((map_ne_zero (σ : E →+* E)).2 hP).isUnit
    have hc : Formalism.UG.cT (σ : E →+* E) (P.map (σ : E →+* E)) = Pᵀ := by
      ext i j
      simp [Formalism.UG.cT, hσ]
    refine ⟨P.map (σ : E →+* E), (P.map (σ : E →+* E))⁻¹, d, Matrix.mul_nonsing_inv _ hu,
      Matrix.nonsing_inv_mul _ hu, ?_, hdσ, hd0 hG.2⟩
    rw [hc]
    exact hd
  obtain ⟨Q, Qi, d, hQ1, hQ2, hQd, hdσ, hd0⟩ := diag hJ
  obtain ⟨R, Ri, e, hR1, hR2, hRe, heσ, he0⟩ := diag hJ'
  obtain ⟨a, ha0, ha⟩ := exists_integer_conj_eq_neg h
  have ha0' : (a : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha0
  filter_upwards [eventually_intM_JR (F := F) Q, eventually_intM_JR (F := F) Qi, eventually_intM_JR (F := F) R,
    eventually_intM_JR (F := F) Ri,
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (e i / d i),
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (d i / e i),
    eventually_one_tmul_mem_intLoc (F := F) (2 * (a : E))⁻¹] with v h1 h2 h3 h4 h5 h6 h7
  have hed : ∀ i, e i / d i * (d i / e i) = 1 := fun i => by
    rw [div_mul_div_comm, mul_comm (e i), div_self (mul_ne_zero (hd0 i) (he0 i))]
  have hc : ∀ i, ∃ c : intLoc F E v, c.1 * sigR (Fv F v) σ c.1 = inclR (Fv F v) (e i / d i) := fun i =>
    exists_norm_eq_at hσ v a ha ha0' (tmul_mem_intLoc (one_mem _) a) h7 ⟨_, h5 i⟩
      (by
        change inclR (Fv F v) (σ (e i / d i)) = inclR (Fv F v) (e i / d i)
        rw [map_div₀, hdσ, heσ])
      (IsUnit.of_mul_eq_one (⟨_, h6 i⟩ : intLoc F E v) (Subtype.ext (by
        change inclR (Fv F v) (e i / d i) * inclR (Fv F v) (d i / e i) = 1
        rw [← map_mul, hed, map_one])))
  choose c hc using hc
  set s := sigR (Fv F v) σ with hs
  let C : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.diagonal fun i => (c i).1
  let C' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    Matrix.diagonal fun i => s (c i).1 * inclR (Fv F v) (d i / e i)
  have hCC : C * C' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← mul_assoc, hc i, ← map_mul, hed, map_one]
  have hC'C : C' * C = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm, ← mul_assoc, hc i, ← map_mul, hed, map_one]
  let u := JR (Fv F v) Q * C * JR (Fv F v) Ri
  let u' := JR (Fv F v) R * C' * JR (Fv F v) Qi
  have huu : u * u' = 1 := by
    calc u * u' = JR (Fv F v) Q * C * (JR (Fv F v) (Ri * R)) * C' * JR (Fv F v) Qi := by
          simp only [u, u', JR_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [hR2, JR_one, Matrix.mul_one, Matrix.mul_assoc (JR (Fv F v) Q), hCC, Matrix.mul_one, ← JR_mul, hQ1,
            JR_one]
  have huu' : u' * u = 1 := by
    calc u' * u = JR (Fv F v) R * C' * (JR (Fv F v) (Qi * Q)) * C * JR (Fv F v) Ri := by
          simp only [u, u', JR_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [hQ2, JR_one, Matrix.mul_one, Matrix.mul_assoc (JR (Fv F v) R), hC'C, Matrix.mul_one, ← JR_mul, hR1,
            JR_one]
  have hCint : IntM v C := intM_diagonal fun i => (c i).2
  have hC'int : IntM v C' := intM_diagonal fun i => mul_mem (sigR_mem_intLoc σ (c i).2) (h6 i)
  have hui : IntM v u := intM_mul (intM_mul h1 hCint) h4
  have hu'i : IntM v u' := intM_mul (intM_mul h3 hC'int) h2
  have eC : Formalism.UG.cT s C * Matrix.diagonal (fun i => inclR (Fv F v) (d i)) * C =
      Matrix.diagonal fun i => inclR (Fv F v) (e i) := by
    rw [cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [show s (c i).1 * inclR (Fv F v) (d i) * (c i).1 = (c i).1 * s (c i).1 * inclR (Fv F v) (d i) by ring, hc i,
      ← map_mul, div_mul_cancel₀ _ (hd0 i)]
  refine ⟨⟨u, u', huu, huu'⟩, ?_, fun y => ?_⟩
  · change Formalism.UG.cT s u * JR (Fv F v) J * u = JR (Fv F v) J'
    have k1 : Formalism.UG.cT s u * JR (Fv F v) J * u = JR (Fv F v) (Formalism.UG.cT (σ : E →+* E) Ri) *
        (Formalism.UG.cT s C * JR (Fv F v) (Formalism.UG.cT (σ : E →+* E) Q * J * Q) * C) * JR (Fv F v) Ri := by
      simp only [u, Formalism.UG.cT_mul, hs, cT_JR, JR_mul, Matrix.mul_assoc]
    rw [k1, hQd, JR_diagonal, eC, ← JR_diagonal, ← hRe, ← JR_mul, ← JR_mul]
    congr 1
    calc Formalism.UG.cT (σ : E →+* E) Ri * (Formalism.UG.cT (σ : E →+* E) R * J' * R) * Ri =
        (Formalism.UG.cT (σ : E →+* E) Ri * Formalism.UG.cT (σ : E →+* E) R) * J' * (R * Ri) := by
          simp only [Matrix.mul_assoc]
      _ = J' := by rw [← Formalism.UG.cT_mul, hR1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · change u *ᵥ y ∈ latLoc F (stdLattice E n) v ↔ y ∈ latLoc F (stdLattice E n) v
    rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
    refine ⟨fun hy => ?_, fun hy => mulVec_mem hui hy⟩
    have := mulVec_mem hu'i hy
    rwa [Matrix.mulVec_mulVec, huu', Matrix.one_mulVec] at this

end GlobalTheory.HermCongAlmostAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → Nontrivial R₂.HK.V → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → IsCoverIt R₁ R₂ B → ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  first | exact @GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt | exact GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt | (intros; apply GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightBruhatFundamentalDomainCentralizerStatement
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_bruhat_fundamental_domain_centralizer : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), IsMulCommutative (cent γ) → ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)), IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → ∃ α : H → ℝ≥0∞, Measurable α ∧ (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) ∧ ∀ ψ : H → ℝ≥0∞, Measurable ψ → LeftInv (cent γ) ψ → ∫⁻ y, α y * ψ y ∂μ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
  first | exact @GlobalTheory.WeightUnfold.exists_weight | exact GlobalTheory.WeightUnfold.exists_weight | (intros; apply GlobalTheory.WeightUnfold.exists_weight <;> assumption)
end

