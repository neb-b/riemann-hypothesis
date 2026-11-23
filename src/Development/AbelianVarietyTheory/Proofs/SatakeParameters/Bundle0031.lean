module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalRingCardinality.DataRows
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
public import Formalism.LocalRingCardinality.Params
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitLiftOfLiftParam

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemBiSupOfOrthogonal
section
noncomputable section

namespace GlobalTheory.DownMemRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

theorem mem_biSup_of_orthogonal {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (S : Set ι) (htop : ⨆ k, U k = ⊤) (horth : ∀ k k', k ≠ k' → U k ⟂ U k')
    {v : V} (hv : ∀ k ∉ S, v ∈ (U k)ᗮ) : v ∈ ⨆ k ∈ S, U k := by
  have hsup : (⨆ k ∈ S, U k) ⊔ (⨆ k ∈ Sᶜ, U k) = ⊤ := by
    rw [← htop]
    exact (iSup_split U (· ∈ S)).symm
  have ho : (⨆ k ∈ S, U k) ⟂ (⨆ k ∈ Sᶜ, U k) := by
    simp only [Submodule.isOrtho_iSup_left, Submodule.isOrtho_iSup_right]
    intro k hk k' hk'
    refine horth _ _ ?_
    rintro rfl
    exact absurd hk' hk
  have hv' : v ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have h1 : (ℂ ∙ v) ⟂ (⨆ k ∈ Sᶜ, U k) := by
      simp only [Submodule.isOrtho_iSup_right]
      intro k hk
      exact (Submodule.span_singleton_le_iff_mem _ _).2 (hv k hk)
    exact h1 (Submodule.mem_span_singleton_self v)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hsup.ge (Submodule.mem_top (x := v)))
  have hb' : b ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have := Submodule.sub_mem _ hv' (ho ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hb' b hb)
  rw [hb0, add_zero]
  exact ha

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem hasParamW_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i)
    (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig)
    {σ : what₂.FT} {P : A.AV i} (hθ : thetaOf N A i σ P) (hP : A.ptV i P = some x) :
    HasParamW N A i σ Sig := by
  obtain ⟨P', hP', h1, -, h3, h4, -⟩ := hx
  refine ⟨fun p hp => ?_, ?_, fun w hw => ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · have e : rankIso N A Sig + R.t = R.nV := by
      rw [← h3]
      simp [rankIso, twistIso, muPart, Function.comp_def]
    have e' : R.nV = R.r + R.t := rfl
    omega
  · have e := hloc P' P x hP' hP w hw
    rw [← h4 w hw, ParUpRoad.isoLoc_lift N A hL, hS σ P hθ w hw] at e
    exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem typeV_isOrtho_eigC {i : N.Loc} (hT : TypeOrth N A i) {x : N.X i} {P : A.AV i}
    (hP : A.ptV i P ≠ some x) : A.typeV i P ⟂ eigC N A i x := by
  unfold eigC
  simp only [Submodule.isOrtho_iSup_right]
  intro P' hP'
  refine hT P P' ?_
  rintro rfl
  exact hP hP'

theorem thetaP_mem (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A) {i : N.Loc}
    (htop : ⨆ σ, what₂.isot (N.j i) σ = ⊤) (hO : PartOrth N i) (hT : TypeOrth N A i)
    (hS : SplitLift N A i) (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)}
    (hx : HasParamX N A i x Sig) {F : what₂.Mt (N.mu i) (N.j i)} (hF : F ∈ eigC N A i x) :
    what₂.thetaP (N.mu i) (N.j i) F ∈ MjSig N A i Sig := by
  refine mem_biSup_of_orthogonal (what₂.isot (N.j i)) {σ | HasParamW N A i σ Sig} htop hO
    fun σ hσ => ?_
  by_cases h0 : what₂.isot (N.j i) σ = ⊥
  · rw [h0, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  obtain ⟨P, hP⟩ := hθ i σ h0
  have hne : A.ptV i P ≠ some x := fun h => hσ (hasParamW_of_thetaOf N A hL hS hloc hx hP h)
  rw [Submodule.mem_orthogonal]
  intro f hf
  rw [← LinearMap.adjoint_inner_left]
  exact (typeV_isOrtho_eigC N A hT hne).inner_eq (hP.2 ⟨f, hf, rfl⟩) hF

theorem downMem : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), ThetaOne N A → Rows.IsotInternal what₂ → PartOrth N i → TypeOrth N A i → ParamLaws N A →
      SplitLift N A i → LocOfPt N A i → DownMem N A i := by
  rintro R H what₂ N A i hθ hI hO hT hL hS hloc x - Sig hx _ ⟨F, hF, rfl⟩
  exact thetaP_mem N A hθ hL (hI _ (N.j_range i).1 (N.j_range i).2).submodule_iSup_eq_top hO hT hS hloc hx hF

end GlobalTheory.DownMemRoad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RenameUpperLeftCornerMemWeylLattice
section
open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory

namespace WeylRankEmbed

variable (R : Type) [CommRing R] {a b : ℕ} (hab : a ≤ b)

abbrev corner : Fin a × Fin a → Fin b × Fin b :=
  fun v => (Fin.castLE hab v.1, Fin.castLE hab v.2)

theorem rename_lpMinor (s : ℕ) (h1 : s ≤ a) (h2 : s ≤ b) :
    rename (corner hab) (lpMinor R s h1 h1) = lpMinor R s h2 h2 := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [corner]

theorem rename_hw (ν : Fin a → ℕ) (ν' : Fin b → ℕ)
    (h : ∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) :
    rename (corner hab) (hw R le_rfl ν) = hw R le_rfl ν' := by
  unfold hw
  rw [map_prod]
  symm
  refine (Finset.prod_of_injOn (Fin.castLE hab) ((Fin.castLE_injective hab).injOn)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_).symm
  · intro j _ hj
    have hja : ¬ (j : ℕ) < a := by
      intro hlt
      exact hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
    rw [h j, dite_eq_right hja]
    simp
  · intro i _
    rw [map_pow, rename_lpMinor R hab _ _ (by have := i.2; omega)]
    have e1 : ν' (Fin.castLE hab i) = ν i := by
      rw [h, dite_eq_left (by simp)]
      rfl
    have e2 : nuNext ν' (Fin.castLE hab i) = nuNext ν i := by
      unfold nuNext
      by_cases h1 : (i : ℕ) + 1 < a
      · rw [dite_eq_left h1, dite_eq_left (by simp; omega), h, dite_eq_left (by simpa using h1)]
        rfl
      · rw [dite_eq_right h1]
        split_ifs with h2
        · rw [h, dite_eq_right (by simpa using h1)]
        · rfl
    rw [e1, e2]
    rfl

theorem rename_rowDiv (x y : Fin a) (k : ℕ) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (rowDiv R x y k f) =
      rowDiv R (Fin.castLE hab x) (Fin.castLE hab y) k (rename (corner hab) f) := by
  have key : (Polynomial.mapAlgHom (rename (R := R) (corner hab))).comp (rowGen R x y) =
      (rowGen R (Fin.castLE hab x) (Fin.castLE hab y)).comp (rename (corner hab)) := by
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v.1 = y
    · simp [rowGen, hv, corner]
    · have hv' : Fin.castLE hab v.1 ≠ Fin.castLE hab y := fun e => hv (Fin.castLE_injective hab e)
      simp [rowGen, hv, corner]
  have h2 := congrArg (fun φ => (φ f).coeff k) key
  simpa [rowDiv, Polynomial.coeff_map] using h2

theorem rename_applyWord (w : List (Fin a × Fin a × ℕ)) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (applyWord R w f) =
      applyWord R (w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2))
        (rename (corner hab) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons, List.map_cons] at ih ⊢
    rw [rename_rowDiv, ih]

end WeylRankEmbed

theorem weyl_rename_castLE_mem :
    ∀ (R : Type) [CommRing R] (a b : ℕ) (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ), (∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) → ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R a a le_rfl ν, MvPolynomial.rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f ∈ Formalism.GradedWeylDivisibility.weyl R b b le_rfl ν' := by
  intro R _ a b hab ν ν' h f hf
  change rename (WeylRankEmbed.corner hab) f ∈ _
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2), ?_⟩
    simp only
    rw [WeylRankEmbed.rename_applyWord, WeylRankEmbed.rename_hw R hab ν ν' h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RiemannFormHermitianLattice
section
open KaehlerDifferential GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem mOm_ιMulti_D_algebraMap (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] (q : ℕ) (w : Fin q → A) :
    ((semiHom_algebraMap k A K).mOm q (exteriorPower.ιMulti A q fun j => D k A (w j)) : DR k K) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (algebraMap A K (w j)) := by
  rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact (SemiHom.mDR_ι _ _).trans (congrArg _ (SemiHom.m1_D _ _))

theorem mOm_injective_and_omB (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] [Algebra.Smooth k A]
    (B : Subalgebra k K) (hB : ∀ y, y ∈ B ↔ ∃ f : A, algebraMap A K f = y) (q : ℕ) :
    Function.Injective ((semiHom_algebraMap k A K).mOm q) ∧
      ∀ y : DR k K, y ∈ omB k K B q ↔
        ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y := by
  haveI : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)
  haveI : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)
  have hE : IsLocalizedModule (nonZeroDivisors A) (formLin k A K q) :=
    (isLocalizedModule_iff_isBaseChange _ K _).2 (isBaseChange_formLin k A K q)
  haveI : Module.Projective A (⋀[A]^q Ω[A⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A Ω[A⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination A id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat A (⋀[A]^q Ω[A⁄k]) := inferInstance
  haveI : Module.IsTorsionFree A (⋀[A]^q Ω[A⁄k]) := Module.Flat.isTorsionFree
  have hinj : Function.Injective (formLin k A K q) := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[A]^q Ω[A⁄k])
      (isRegular_iff_ne_zero.mpr (nonZeroDivisors.coe_ne_zero c))) hc
  have hsm : ∀ (a : A) (z : Om k A q), ((semiHom_algebraMap k A K).mOm q (a • z) : DR k K) =
      algebraMap A K a • ((semiHom_algebraMap k A K).mOm q z : DR k K) := fun a z => by
    rw [SemiHom.mOm_smul]; rfl
  refine ⟨hinj, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · let S : Submodule k (DR k K) :=
      { carrier := {y | ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y}
        add_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a + b, by rw [map_add (f := _)]; rfl⟩
        zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
        smul_mem' := by
          rintro c _ ⟨a, rfl⟩
          refine ⟨algebraMap k A c • a, ?_⟩
          rw [hsm, ← IsScalarTower.algebraMap_apply, algebraMap_smul] }
    have : omB k K B q ≤ S := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := (hB b).1 hb
      choose w hw using fun j => (hB (v j)).1 (hv j)
      refine ⟨a • exteriorPower.ιMulti A q (fun j => D k A (w j)), ?_⟩
      rw [hsm, mOm_ιMulti_D_algebraMap]
      simp only [hw]
    exact this hy
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span A q Ω[A⁄k] (span_range_derivation k A)
    have hz : z ∈ Submodule.span A
        (⇑(exteriorPower.ιMulti A q) '' {a | Set.range a ⊆ Set.range (D k A)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k A (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [mOm_ιMulti_D_algebraMap]
      exact ιMulti_D_mem_omB_regForms B q fun j => ⟨algebraMap A K (w j), (hB _).2 ⟨w j, rfl⟩⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact add_mem h1 h2
    | smul a z _ h => rw [hsm]; exact smul_mem_omB_regForms B q ((hB _).2 ⟨a, rfl⟩) h

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
section
noncomputable section

namespace GlobalTheory.Proof.SplitPlaceGoodSignature

open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem isSplitPl_of_not_isConjPl (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E))
    (h : ¬ IsConjPl H w w) : IsSplitPl H w := by
  by_contra hs
  apply h
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  have hc : ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y = c x := fun x y hy =>
    RingOfIntegers.ext hy
  have hle : w.asIdeal ≤ w.asIdeal.comap c := by
    intro x hx
    by_contra hx'
    exact hs ⟨x, hx, fun y hy => by rw [hc x y hy]; exact hx'⟩
  have heq : w.asIdeal = w.asIdeal.comap c :=
    w.isMaximal.eq_of_le (Ideal.comap_ne_top c w.isPrime.ne_top) hle
  intro x y hy
  rw [hc x y hy, ← Ideal.mem_comap, ← heq]

variable (N : NData R H what₂) (A : NAut N)

theorem typePlSplit : TypePlSplit N A := fun k v =>
  isSplitPl_of_not_isConjPl _ (A.plGw_nconj k v v)

theorem isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [Check.iso_char N A hL, Check.iso_append]
  rfl

theorem goodRow_iff_goodSig {i : N.Loc} {σ : what₂.FT} {Sig : List (Part A.CG)}
    (h : ∀ w, IsSplitPl H w → isoLoc N A Sig w = A.locW i σ w) :
    N.goodRow σ ↔ goodSig N A Sig := by
  have hl : ∀ k, (fun v => A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))) = N.lab k σ := by
    intro k
    funext v
    rw [h _ (typePlSplit N A k v), A.lab_loc i k σ v]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [hl k]

theorem isoLoc_eq_of_hasParamX (hL : ParamLaws N A) {i : N.Loc} (hloc : LocOfPt N A i) {x : N.X i}
    {Sig Sig' : List (Part A.CG)} (h : HasParamX N A i x Sig) (h' : HasParamX N A i x Sig')
    (w : PlE H) (hw : IsSplitPl H w) : isoLoc N A Sig w = isoLoc N A Sig' w := by
  obtain ⟨P, hP, hB⟩ := h
  obtain ⟨P', hP', hB'⟩ := h'
  have e := hloc P P' x hP hP' w hw
  rw [← hB.2.2.2.1 w hw, ← hB'.2.2.2.1 w hw, isoLoc_lift N A hL, isoLoc_lift N A hL] at e
  exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem goodPart_of_lifts (i : N.Loc) (h1 : ThetaOne N A) (hL : ParamLaws N A)
    (hlift : LiftParam N A i) (hpt : PtLocal N A i) (hloc : LocOfPt N A i) : GoodPart N A i := by
  unfold GoodPart goodPartM
  apply le_antisymm
  · refine iSup₂_le fun σ hσ => ?_
    obtain ⟨hg, Sig₀, hW₀, x₀, hx₀⟩ := hσ
    by_cases hb : what₂.isot (N.j i) σ = ⊥
    · rw [hb]; exact bot_le
    obtain ⟨P, hP⟩ := h1 i σ hb
    obtain ⟨Sig, hW, hB⟩ := hlift σ P hP
    obtain ⟨y, hy⟩ := hpt P x₀ fun w hw => by
      obtain ⟨p, hp, hp'⟩ := hx₀ w hw
      refine ⟨p, ?_, hp'⟩
      rw [hp, ← hB.2.2.2.1 w hw.1, isoLoc_lift N A hL, isoLoc_lift N A hL, hW₀.2.2 w hw.1,
        hW.2.2 w hw.1]
    have hX : HasParamX N A i y Sig := ⟨P, hy, hB⟩
    have hZ : y ∈ ZgoodN N A i := by
      refine ⟨⟨P, hy, _, hB, ?_⟩, Sig, hX, (goodRow_iff_goodSig N A hW.2.2).1 hg⟩
      exact List.mem_map.2 ⟨muPart N A i, by simp, rfl⟩
    refine le_iSup₂_of_le y hZ (le_iSup₂_of_le Sig hX ?_)
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | HasParamW N A i σ Sig}) =>
      what₂.isot (N.j i) σ) σ hW le_rfl
  · refine iSup₂_le fun x hx => iSup₂_le fun Sig hX => ?_
    unfold MjSig
    refine iSup₂_le fun σ hW => ?_
    obtain ⟨-, Sig', hX', hg⟩ := hx
    have hgood : N.goodRow σ := (goodRow_iff_goodSig N A (i := i) fun w hw =>
      (isoLoc_eq_of_hasParamX N A hL hloc hX' hX w hw).trans (hW.2.2 w hw)).2 hg
    have hat : AtM N A i σ := by
      obtain ⟨P, hP, hB⟩ := hX
      refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
      rw [hB.2.2.2.1 w hw.1]
      exact A.pt_loc i P x hP w hw
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | N.goodRow σ ∧ AtM N A i σ}) =>
      what₂.isot (N.j i) σ) σ ⟨hgood, hat⟩ le_rfl

end GlobalTheory.Proof.SplitPlaceGoodSignature
end
end

