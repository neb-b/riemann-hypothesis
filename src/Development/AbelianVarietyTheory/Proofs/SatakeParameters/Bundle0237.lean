module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedOfFixedByLocalLevels
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLevFix

open GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU (E := E) (n := a)) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  have hinf : cInf x = 1 := MonoidHom.mem_ker.1 hx
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij] <;> rfl

theorem isCompact_integral :
    IsCompact {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} := by
  have e' : ∀ k : finU (E := E) (n := a), k ∈ (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap
      (GlobalTheory.BCT.GlobLev.finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
    intro k
    rw [Subgroup.mem_comap, GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  have e : {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} =
      ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
        Set (finU (E := E) (n := a))) := by
    ext k
    exact (e' k).symm
  have hO : IsOpen ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
      Set (finU (E := E) (n := a))) :=
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a).preimage GlobalTheory.BCT.GlobLev.continuous_finPart
  rw [e]
  refine IsCompact.of_isClosed_subset (GlobalTheory.BCT.GlobLev.isClosedEmbedding_finU.isCompact_preimage
      ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E a).image GlobalTheory.BCT.GlobLev.continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨GlobalTheory.BCT.GlobLev.finPart E a x, hx, ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_finite_fix {φ : UA E a → ℂ} (hφ : IsAutFormU φ) :
    ∃ t : Finset (HeightOneSpectrum (𝓞 E)), ∀ k ∈ finU (E := E) (n := a), (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ u ∈ t, cLoc u k = 1) → RU E a k φ = φ := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) := fun u =>
    Units.isEmbedding_embedProduct.t2Space
  have hc := (isCompact_integral (E := E) (a := a)).diff hφ.level
  have hcov : {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} \ {k : finU (E := E) (n := a) | RU E a k φ = φ} ⊆
      ⋃ u, {k : finU (E := E) (n := a) | cLoc u k.1 ≠ 1} := by
    rintro k ⟨-, hk⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hne
    push_neg at hne
    apply hk
    show RU E a k.1 φ = φ
    rw [eq_one_of_forall_cLoc k.2 hne, map_one]
    rfl
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _ (fun u => isOpen_ne_fun
    ((GlobalTheory.BCT.GlobLev.continuous_cLoc u).comp continuous_subtype_val) continuous_const) hcov
  refine ⟨t, fun k hk hint h1 => ?_⟩
  by_contra hne
  have := ht (show (⟨k, hk⟩ : finU (E := E) (n := a)) ∈ _ from ⟨hint, hne⟩)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
  obtain ⟨u, hu, hne'⟩ := this
  exact hne' (h1 u hu)

theorem one_of_cLoc_eq_one {q : HeightOneSpectrum (𝓞 E)} {z : UA E a} (h : cLoc q z = 1) :
    ∀ u, ¬ Apart u q → cLoc u z = 1 := by
  intro u hu
  by_cases hq : IsSplitAt q
  · exact GlobalTheory.Cong.LevelExt.one_of_cLoc hq z h u hu
  · rw [eq_of_not_apart_of_not_split hq hu]
    exact h

theorem peel (φ : UA E a → ℂ) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ k ∈ finU (E := E) (n := a), (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u (n := a)) → (∀ u ∈ S, cLoc u k = 1) → RU E a k φ = φ)
    (Q : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ x ∈ finU (E := E) (n := a), (∀ u, (∀ q ∈ Q, Apart u q) → (u ∈ S → cLoc u x = 1) ∧ cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ q ∈ Q, ∃ y ∈ locU a q, RU E a y φ = φ ∧ cLoc q y = cLoc q x) → RU E a x φ = φ := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro x hx h1 _
    exact hS x hx (fun u => (h1 u (by simp)).2) (fun u hu => (h1 u (by simp)).1 hu)
  | @insert q Q hqQ ih =>
    intro x hx h1 h2
    obtain ⟨y, hyl, hyφ, hyq⟩ := h2 q (Finset.mem_insert_self q Q)
    have hyf : y ∈ finU (E := E) (n := a) := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).1
    have hya : ∀ u, Apart u q → cLoc u y = 1 := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2
    have hq1 : cLoc q (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyq, inv_mul_cancel]
    have hfib : ∀ u, ¬ Apart u q → cLoc u (y⁻¹ * x) = 1 := one_of_cLoc_eq_one hq1
    have happ : ∀ u, Apart u q → cLoc u (y⁻¹ * x) = cLoc u x := fun u hu => by
      rw [map_mul, map_inv, hya u hu, inv_one, one_mul]
    have key : RU E a (y⁻¹ * x) φ = φ := by
      refine ih (y⁻¹ * x) (mul_mem (inv_mem hyf) hx) (fun u hu => ?_) (fun q' hq' => ?_)
      · by_cases huq : Apart u q
        · rw [happ u huq]
          exact h1 u (fun p hp => by
            rcases Finset.mem_insert.1 hp with rfl | hp
            · exact huq
            · exact hu p hp)
        · rw [hfib u huq]
          exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
      · by_cases hqq : Apart q' q
        · obtain ⟨y', hy'l, hy'φ, hy'q⟩ := h2 q' (Finset.mem_insert_of_mem hq')
          exact ⟨y', hy'l, hy'φ, hy'q.trans (happ q' hqq).symm⟩
        · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl, by rw [map_one, hfib q' hqq]⟩
    have hxe : x = y * (y⁻¹ * x) := by rw [mul_inv_cancel_left]
    rw [hxe, map_mul, Module.End.mul_apply, key, hyφ]

end GlobalTheory.Cong.AdaptLevFix


open GlobalTheory.Cong.AdaptLevFix in
theorem GlobalTheory.Cong.AdaptLev.fixed_of_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → ∀ φ : UA E a → ℂ, IsAutFormU φ → (∀ w, Apart w w₀ → ∀ x ∈ H w, RU E a x φ = φ) → ∀ x ∈ GlobalTheory.Cong.AdaptLev.levelOf a w₀ H, RU E a x φ = φ := by
  intro E _ _ _ a w₀ H hHle _ _ _ hcof φ hφ hfix x hx
  classical
  obtain ⟨t, ht⟩ := exists_finite_fix hφ
  have hT : {w | ¬ H w = intU a w}.Finite := Filter.eventually_cofinite.1 hcof
  let Q : Finset (HeightOneSpectrum (𝓞 E)) := (t ∪ hT.toFinset).filter (fun w => Apart w w₀)
  obtain ⟨hxf, hx1, hxH⟩ := mem_levelOf.1 hx
  refine peel φ (t : Set _) (fun k hk hi h1 => ht k hk hi h1) Q x hxf (fun u hu => ?_) (fun q hq => ?_)
  · by_cases hu0 : Apart u w₀
    · have huQ : u ∉ Q := fun h => hu u h rfl
      have hut : u ∉ t := fun h => huQ (Finset.mem_filter.2 ⟨Finset.mem_union_left _ h, hu0⟩)
      have huT : H u = intU a u := by
        by_contra h
        exact huQ (Finset.mem_filter.2 ⟨Finset.mem_union_right _ (hT.mem_toFinset.2 h), hu0⟩)
      obtain ⟨y, hy, hyx⟩ := hxH u hu0
      rw [huT] at hy
      refine ⟨fun h => absurd h hut, ?_⟩
      rw [← hyx]
      exact (mem_intU.1 hy).2 u (fun h => h rfl)
    · rw [hx1 u hu0]
      exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
  · have hq0 : Apart q w₀ := (Finset.mem_filter.1 hq).2
    obtain ⟨y, hy, hyx⟩ := hxH q hq0
    exact ⟨y, hHle q hy, hfix q hq0 y hy, hyx⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieGalAssembly

theorem potCrysIffWD (D : D7) : PotCrysIffWD D.nd D.naut := by
  intro i a r w hw hr
  refine ⟨fun hc => ?_, fun h => (D.naut.wdOf_mono0L i r w hw hr h.1).1 h.2⟩
  suffices hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_mono0L i r w hw hr hd).2 hc⟩
  have := D.nd.lPrime i
  obtain ⟨L, hle, hL⟩ := _root_.GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) _ a r hr (D.nbr i w hw).LL
  obtain ⟨ρ, hρ, rfl⟩ := GlobalTheory.CrysWD.exists_descent r hr L hL
  obtain ⟨-, h2, h1, -⟩ := (D.loc_tie i w hw).2.2 L hle a ρ hρ
  have := L.2
  obtain ⟨K', hK, hc'⟩ := h1.1 hc
  have h3 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ hc').1
  have h4 := (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hK _ (D.locT (D.nd.l i))).2 h3
  refine h2.2 ?_
  unfold IsDR at h4
  unfold LocBridge.IsdRE
  simpa using h4

end GlobalTheory.TieGalAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLevelAwayDefiniteUnitaryLevelFromLocalLevels
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong.LevAway

open Matrix GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.SplitPts GroundTheory.Automorphic GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem integral_iff (x : UA E a) :
    GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a ↔
      ∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem exists_compact_integral : ∃ C : Set (UA E a), IsCompact C ∧
    ∀ x ∈ finU (E := E) (n := a), (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) → x ∈ C := by
  let Kf : Subgroup (finU (E := E) (n := a)) := (AdelicGLn.integralFiniteGL E a).comap (finPart E a)
  have hO : IsOpen (Kf : Set (finU (E := E) (n := a))) := (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  have hc : IsCompact (Kf : Set (finU (E := E) (n := a))) := by
    refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
    have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  refine ⟨Subtype.val '' (Kf : Set (finU (E := E) (n := a))), hc.image continuous_subtype_val, fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (integral_iff x).2 hi

theorem exists_loc (w : HeightOneSpectrum (𝓞 E)) : ∃ f : UA E a → UA E a, Continuous f ∧
    ∀ x, f x ∈ locU a w ∧ cLoc w (f x) = cLoc w x := by
  by_cases hw : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
    refine ⟨fun x => (e.symm (cLoc w x)).1, continuous_subtype_val.comp (e.symm.continuous.comp (continuous_cLoc w)),
      fun x => ⟨(e.symm _).2, ?_⟩⟩
    rw [← he]; exact e.apply_symm_apply _
  · have hc : conjSrc (conjE E) w = w := conjSrc_eq_of_not_split hw
    have key : ∀ x : UA E a, finGL E a (locGL E a w (cLoc w x)) ∈ UA E a := by
      intro x
      refine finGL_mem_UA _ fun u => ?_
      by_cases hu : u = w
      · subst hu
        have e1 : ∀ v, v = u → GeneralLinearGroup.map (pLoc E v) (locGL E a u (cLoc u x)) = cLoc v x := by
          rintro v rfl; exact pLoc_locGL _ _
        rw [e1 _ hc, e1 u rfl]
        exact comp_eq x u
      · have h3 : conjSrc (conjE E) u ≠ w := fun e => hu (by rw [← conjSrc_conjSrc_cm u, e, hc])
        rw [pLoc_locGL_of_ne hu, pLoc_locGL_of_ne h3]
        simp
    refine ⟨fun x => ⟨finGL E a (locGL E a w (cLoc w x)), key x⟩, ?_, fun x => ⟨?_, ?_⟩⟩
    · exact Continuous.subtype_mk (continuous_finGL_ad.comp ((CuspSub.continuous_locGL w).comp (continuous_cLoc w))) _
    · refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
        Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
      rw [cLoc_finGL]
      exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
    · rw [cLoc_finGL]; exact pLoc_locGL _ _

theorem isClosed_finU : IsClosed ((finU (E := E) (n := a) : Subgroup (UA E a)) : Set (UA E a)) := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : Continuous (cInf (E := E) (n := a)) :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
  exact isClosed_eq hc continuous_const

theorem t2GL (w : HeightOneSpectrum (𝓞 E)) : T2Space (GL (Fin a) (w.adicCompletion E)) :=
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_levelOf (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a))
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) : IsClosed (levelOf a w₀ H : Set (UA E a)) := by
  have e : (levelOf a w₀ H : Set (UA E a)) = (finU (E := E) (n := a) : Set (UA E a)) ∩
      ((⋂ u, ⋂ (_ : ¬ Apart u w₀), {x | cLoc u x = 1}) ∩
        ⋂ w, ⋂ (_ : Apart w w₀), cLoc w ⁻¹' (cLoc w '' (H w : Set (UA E a)))) := by
    ext x
    simp only [SetLike.mem_coe, mem_levelOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_image]
  rw [e]
  refine isClosed_finU.inter (IsClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun w => isClosed_iInter fun _ => ?_))
  · haveI := t2GL (E := E) (a := a) u
    exact isClosed_eq (continuous_cLoc u) continuous_const
  · haveI := t2GL (E := E) (a := a) w
    exact ((hc w).image (continuous_cLoc w)).isClosed.preimage (continuous_cLoc w)

theorem exists_compact_of_finset (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) (hle : ∀ w, H w ≤ locU a w)
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) (R : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ C : Set (UA E a), IsCompact C ∧ ∀ x ∈ finU (E := E) (n := a), (∀ u, (∀ r ∈ R, Apart u r) → cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ r ∈ R, ∃ y ∈ H r, cLoc r y = cLoc r x) → x ∈ C := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    obtain ⟨C, hC, hsub⟩ := exists_compact_integral (E := E) (a := a)
    exact ⟨C, hC, fun x hx hi _ => hsub x hx fun u => hi u (by simp)⟩
  | insert r R hr ih =>
    obtain ⟨C, hC, hsub⟩ := ih
    refine ⟨C * (H r : Set (UA E a)), hC.mul (hc r), fun x hx hi hH => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hH r (Finset.mem_insert_self r R)
    by_cases hap : ∀ r' ∈ R, Apart r' r
    · have hyl := hle r hy
      have hy1 : ∀ u, Apart u r → cLoc u y = 1 := fun u hu => ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2 u hu
      have hyf : y ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hyl).1
      refine ⟨x * y⁻¹, hsub _ (mul_mem hx (inv_mem hyf)) ?_ ?_, y, hy, inv_mul_cancel_right x y⟩
      · intro u hu
        by_cases hur : Apart u r
        · rw [map_mul, map_inv, hy1 u hur, inv_one, mul_one]
          refine hi u fun r' hr' => ?_
          rcases Finset.mem_insert.1 hr' with rfl | h
          · exact hur
          · exact hu r' h
        · have hz : cLoc r (x * y⁻¹) ∈ GlobalTheory.LFun.KGL r (n := a) := by
            rw [map_mul, map_inv, hyx, mul_inv_cancel]; exact one_mem _
          rcases eq_or_eq_conjSrc (not_not.1 hur) with rfl | rfl
          · exact hz
          · exact integral_conjSrc _ r hz
      · intro r' h
        obtain ⟨y', hy', e'⟩ := hH r' (Finset.mem_insert_of_mem h)
        exact ⟨y', hy', by rw [map_mul, map_inv, hy1 r' (hap r' h), inv_one, mul_one]; exact e'⟩
    · push_neg at hap
      obtain ⟨r', hr', hnr⟩ := hap
      have hxC : x ∈ C := by
        refine hsub x hx (fun u hu => hi u fun r'' hr'' => ?_) (fun r'' h => hH r'' (Finset.mem_insert_of_mem h))
        rcases Finset.mem_insert.1 hr'' with rfl | h
        · intro hh
          exact not_apart_trans (not_not.2 hh) (not_apart_symm hnr) (hu r' hr')
        · exact hu r'' h
      exact ⟨x, hxC, 1, one_mem _, mul_one x⟩

theorem isLevelAway_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  intro E _ _ _ a w₀ H hle _ hc ho hcof
  have hT := Filter.eventually_cofinite.1 hcof
  refine ⟨levelOf_le_finU w₀ H, fun x hx => (mem_levelOf.1 hx).2.1, ?_, ?_⟩
  · obtain ⟨C, hC, hsub⟩ := exists_compact_of_finset H hle hc hT.toFinset
    refine hC.of_isClosed_subset (isClosed_levelOf w₀ H hc) fun x hx => ?_
    obtain ⟨hf, h1, hw⟩ := mem_levelOf.1 hx
    refine hsub x hf (fun u hu => ?_) (fun r _ => ?_)
    · have hHu : H u = intU a u := by
        by_contra h
        exact hu u (hT.mem_toFinset.2 h) rfl
      by_cases h0 : Apart u w₀
      · obtain ⟨y, hy, e⟩ := hw u h0
        rw [hHu] at hy
        rw [← e]
        exact (mem_intU.1 hy).2 u (fun h => h rfl)
      · rw [h1 u h0]; exact one_mem _
    · by_cases h0 : Apart r w₀
      · exact hw r h0
      · exact ⟨1, one_mem _, by rw [map_one, h1 r h0]⟩
  · choose f hfc hf using fun w => exists_loc (E := E) (a := a) w
    let g : ∀ w, UA E a → locU a w := fun w x => ⟨f w x, (hf w x).1⟩
    have hg : ∀ w, Continuous (g w) := fun w => (hfc w).subtype_mk _
    have hpf : Continuous fun x : UA E a => GeneralLinearGroup.map (pFin E) (x : GA E a) :=
      (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
        continuous_subtype_val
    refine ⟨{x | GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a} ∩
      ⋂ w ∈ hT.toFinset, g w ⁻¹' ((H w).subgroupOf (locU a w) : Set (locU a w)), ?_, ?_, ?_⟩
    · exact ((AdelicGLn.isOpen_integralFiniteGL E a).preimage hpf).inter
        (isOpen_biInter_finset fun w _ => (ho w).preimage (hg w))
    · refine ⟨(integral_iff 1).2 fun u => by rw [map_one]; exact one_mem _, Set.mem_iInter₂.2 fun w _ => ?_⟩
      have h1 : f w 1 = 1 := eq_one_of_cLoc_eq_one (hf w 1).1 (by rw [(hf w 1).2, map_one])
      show (g w 1).1 ∈ H w
      show f w 1 ∈ H w
      rw [h1]; exact one_mem _
    · intro x hxN hxf hx1
      obtain ⟨hxi, hxH⟩ := hxN
      have hxi' := (integral_iff x).1 hxi
      refine mem_levelOf.2 ⟨hxf, hx1, fun w _ => ⟨f w x, ?_, (hf w x).2⟩⟩
      by_cases hwT : H w = intU a w
      · rw [hwT]; exact mem_intU_of (hf w x).1 (by rw [(hf w x).2]; exact hxi' w)
      · exact Set.mem_iInter₂.1 hxH w (hT.mem_toFinset.2 hwT)

end GlobalTheory.Cong.LevAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstOfCoordRev
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open TensorProduct Module GlobalTheory.CoeffExt

namespace GlobalTheory.SstModel

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_of_coord_rev [Nonempty ι] (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ') :
    IsSst P ρ := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [GlobalTheory.AboveL.RepConj.isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, GlobalTheory.AboveL.RepConj.finrank_pi_card,
    GlobalTheory.AboveL.RepConj.finrank_pi_card, mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos h

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_of_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1)
    (h : IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :
    IsSst P (Bw.repE L₁ r₁) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have : Nonempty (Fin (finrank ↥L₁.1 ↥L₂.1)) := ⟨⟨0, finrank_pos⟩⟩
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord_rev P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSst_of_isModel {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {r : ↥Gw →* GL (Fin m) (Om l)}
    {L : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥L.1} (hm : IsModel Bw r L r') (hs : IsSstAt P Bw r) :
    IsSst P (Bw.repE L r') := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := hs
  have l₁ : L₁.1 ≤ (supExt L₁ L).1 := le_sup_left
  have l₂ : L.1 ≤ (supExt L₁ L).1 := le_sup_right
  have e := IsModel.unique Bw r (h₁.enlarge l₁) (hm.enlarge l₂)
  have h3 := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hp
  rw [e] at h3
  exact isSst_of_enlarge P Bw l₂ r' h3

end GlobalTheory.SstModel

namespace GlobalTheory.SstModel

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (LL' : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL'.1), IsModel Bw r LL' r' → IsSstAt P Bw r → IsSst P (Bw.repE LL' r') := by
  intro l _ P AI _ E Ω _ _ _ Gw O _ _ _ Bw a r LL' r' hm hs
  exact isSst_of_isModel P hm hs

end GlobalTheory.SstModel

end
end

