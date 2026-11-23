module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOfNotApartOfNotSplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def intU (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Subgroup (UA E a) :=
  locU a w ⊓ ⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w), (GlobalTheory.LFun.KGL u (n := a)).comap (cLoc u)

def levelOf (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    Subgroup (UA E a) :=
  finU (E := E) (n := a) ⊓ (⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w₀), (cLoc u).ker) ⊓
    ⨅ (w : HeightOneSpectrum (𝓞 E)) (_ : Apart w w₀), ((H w).map (cLoc w)).comap (cLoc w)

variable {a : ℕ}

theorem mem_intU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} :
    x ∈ intU a w ↔ x ∈ locU a w ∧ ∀ u, ¬ Apart u w → cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  simp only [intU, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem mem_levelOf {w₀ : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)} {x : UA E a} :
    x ∈ levelOf a w₀ H ↔ x ∈ finU (E := E) (n := a) ∧ (∀ u, ¬ Apart u w₀ → cLoc u x = 1) ∧
      ∀ w, Apart w w₀ → ∃ y ∈ H w, cLoc w y = cLoc w x := by
  simp only [levelOf, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_ker, Subgroup.mem_map, and_assoc]

theorem not_apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart w u) : ¬ Apart u w := fun h' => h (Ne.symm h')

theorem not_apart_trans {w u v : HeightOneSpectrum (𝓞 E)} (h1 : ¬ Apart w u) (h2 : ¬ Apart u v) : ¬ Apart w v :=
  fun h => h ((not_not.1 h1).trans (not_not.1 h2))

theorem locU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : locU a u = locU a w := by
  have e : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := not_not.1 h
  unfold locU
  rw [e]

theorem intU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : intU a u = intU a w := by
  ext x
  rw [mem_intU, mem_intU, locU_congr h]
  exact and_congr_right fun _ => forall_congr' fun v =>
    ⟨fun h' hv => h' (not_apart_trans hv (not_apart_symm h)), fun h' hv => h' (not_apart_trans hv h)⟩

theorem intU_le_locU (w : HeightOneSpectrum (𝓞 E)) : intU a w ≤ locU a w := inf_le_left

theorem levelOf_le_finU (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    levelOf a w₀ H ≤ finU (E := E) (n := a) := fun _ hx => (mem_levelOf.1 hx).1

theorem eq_of_not_apart_of_not_split {w u : HeightOneSpectrum (𝓞 E)} (hw : ¬ IsSplitAt w) (h : ¬ Apart u w) : u = w := by
  by_contra hne
  exact hw ⟨u, hne, not_not.1 h⟩

theorem cLoc_mem_KGL_of_not_apart {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) (x : UA E a)
    (hx : cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) : cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (E := E) (not_not.1 h) with rfl | rfl
  · exact hx
  · exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w hx

theorem mem_intU_of {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (hk : cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) :
    x ∈ intU a w :=
  mem_intU.2 ⟨hx, fun _ hu => cLoc_mem_KGL_of_not_apart hu x hk⟩

theorem eq_one_of_cLoc_eq_one {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (h1 : cLoc w x = 1) :
    x = 1 := by
  by_cases hw : IsSplitAt w
  · exact congrArg Subtype.val (GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨x, hx⟩ h1)
  · have hall : ∀ u, cLoc u x = 1 := by
      intro u
      by_cases hu : Apart u w
      · exact ((GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx).2 u hu
      · rw [eq_of_not_apart_of_not_split hw hu]; exact h1
    have hinf : cInf x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact hinf.trans (map_one _).symm
    · rw [Subgroup.coe_one, map_one]
      refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
      have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (hall u)
      simp only [Units.val_one, Matrix.one_apply] at this
      refine this.trans ?_
      split_ifs with hij <;> simp [hij] <;> rfl

theorem eq_of_cLoc_eq {w : HeightOneSpectrum (𝓞 E)} {x y : UA E a} (hx : x ∈ locU a w) (hy : y ∈ locU a w)
    (h : cLoc w x = cLoc w y) : x = y := by
  have := eq_one_of_cLoc_eq_one (mul_mem hx (inv_mem hy)) (by rw [map_mul, map_inv, h, mul_inv_cancel])
  exact mul_inv_eq_one.1 this

theorem coe_subgroupOf_image {G : Type} [Group G] {H L : Subgroup G} (h : H ≤ L) :
    Subtype.val '' ((H.subgroupOf L : Subgroup L) : Set L) = (H : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, h hx⟩, hx, rfl⟩

theorem isCompact_of_le {w : HeightOneSpectrum (𝓞 E)} {H : Subgroup (UA E a)} (hH : H ≤ intU a w)
    (ho : IsOpen ((H.subgroupOf (locU a w)) : Set (locU a w))) (hc : IsCompact (intU a w : Set (UA E a))) :
    IsCompact (H : Set (UA E a)) := by
  have hcl : IsClosed ((H.subgroupOf (locU a w)) : Set (locU a w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc' : IsCompact (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, coe_subgroupOf_image (intU_le_locU w)]
    exact hc
  have h2 := (hc'.of_isClosed_subset hcl fun x hx => hH hx).image continuous_subtype_val
  rwa [coe_subgroupOf_image (hH.trans (intU_le_locU w))] at h2

end GlobalTheory.Cong.AdaptLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfCharpoly
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveL.AbSub

open Polynomial Module

theorem eq_one_of_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hs : f.IsSemisimple) (hc : f.charpoly = (X - 1) ^ finrank ℂ V) : f = 1 := by
  have h1 : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hs
  have h2 : IsNilpotent (f - algebraMap ℂ (Module.End ℂ V) 1) := by
    refine ⟨finrank ℂ V, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa [map_pow, map_sub, aeval_X, map_one] using this
  have := Module.End.eq_zero_of_isNilpotent_isSemisimple h2 h1
  rw [map_one] at this
  exact sub_eq_zero.mp this

end GlobalTheory.AboveL.AbSub

namespace GlobalTheory.AboveL.AbSub

theorem exists_open_sub : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (y : WD h), AbW y → ∀ σ : Weil h, deg σ ≠ 0 → ∃ V : Subgroup (Dec (F := K) A), IsOpen (V : Set (Dec (F := K) A)) ∧ commutator (Dec (F := K) A) ≤ V ∧ (⟨(σ : G K Ω), Weil_le_Dec h σ.2⟩ : Dec (F := K) A) ∈ V ∧ ∀ τ : Ine (F := K) A, ∀ g ∈ V, (g : G K Ω) = τ → y.charPol (ineIncl h τ) = (Polynomial.X - 1) ^ y.lpDim := by
  intro K Ω _ _ _ _ _ A v h y hy σ hσ
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  haveI : CompactSpace (Dec (F := K) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  obtain ⟨n0, a, rfl⟩ := WD.exists_rep y
  have hcomm : ∀ g g' : Weil h, a.ρ (g * g' * g⁻¹ * g'⁻¹) = 1 := fun g g' => by
    have := hy g g'
    rw [WD.charPol_mk, WD.lpDim_mk] at this
    exact eq_one_of_charpoly _ (a.semisimple _) this
  have hconj : ∀ w x : Weil h, a.ρ x = 1 → a.ρ (w * x * w⁻¹) = 1 := fun w x hx => by
    rw [map_mul, map_mul, hx, mul_one, ← map_mul, mul_inv_cancel, map_one]
  let J : Subgroup (Dec (F := K) A) :=
    { carrier := {d | (d : G K Ω) ∈ Ine (F := K) A ∧ ∀ hw : (d : G K Ω) ∈ Weil h, a.ρ ⟨d, hw⟩ = 1}
      one_mem' := ⟨(Ine (F := K) A).one_mem, fun _ => map_one a.ρ⟩
      mul_mem' := by
        rintro d1 d2 ⟨h1, h1'⟩ ⟨h2, h2'⟩
        refine ⟨(Ine (F := K) A).mul_mem h1 h2, fun hw => ?_⟩
        have e := map_mul a.ρ ⟨(d1 : G K Ω), Ine_le_Weil h h1⟩ ⟨(d2 : G K Ω), Ine_le_Weil h h2⟩
        rw [h1', h2', one_mul] at e
        exact e
      inv_mem' := by
        rintro d ⟨h1, h1'⟩
        refine ⟨(Ine (F := K) A).inv_mem h1, fun hw => ?_⟩
        have e := map_mul a.ρ ⟨((d⁻¹ : Dec (F := K) A) : G K Ω), hw⟩ ⟨(d : G K Ω), Ine_le_Weil h h1⟩
        rw [h1' (Ine_le_Weil h h1), mul_one] at e
        have e1 : (⟨((d⁻¹ : Dec (F := K) A) : G K Ω), hw⟩ * ⟨(d : G K Ω), Ine_le_Weil h h1⟩ : Weil h) = 1 :=
          Subtype.ext (inv_mul_cancel (d : G K Ω))
        rw [e1, map_one] at e
        exact e.symm }
  have memJ : ∀ d : Dec (F := K) A, d ∈ J ↔ ((d : G K Ω) ∈ Ine (F := K) A ∧
      ∀ hw : (d : G K Ω) ∈ Weil h, a.ρ ⟨d, hw⟩ = 1) := fun _ => Iff.rfl

  obtain ⟨O, hO, hOS⟩ := isOpen_induced_iff.mp a.smooth
  have hO1 : (1 : G K Ω) ∈ O := by
    have : (1 : Ine (F := K) A) ∈ Subtype.val ⁻¹' O := by
      rw [hOS]; exact map_one a.ρ
    exact this
  have hPW : ∀ d : Dec (F := K) A, (d : G K Ω) ∈ O → (d : G K Ω) ∈ Ine (F := K) A → d ∈ J := by
    intro d hd hI
    refine ⟨hI, fun hw => ?_⟩
    have : (⟨(d : G K Ω), hI⟩ : Ine (F := K) A) ∈ Subtype.val ⁻¹' O := hd
    rw [hOS] at this
    exact this
  have hW0 : IsOpen (Subtype.val ⁻¹' O : Set (Dec (F := K) A)) := hO.preimage continuous_subtype_val
  obtain ⟨U0, hU0⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW0 hO1
  haveI := U0.toSubgroup.quotient_finite_of_isOpen U0.isOpen
  let ι : Weil h →* Dec (F := K) A := Subgroup.inclusion (Weil_le_Dec h)
  obtain ⟨n, hn, -, hσn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := U0.toSubgroup)) (ι σ)
  have hm : 0 < n * (deg σ).natAbs := Nat.mul_pos hn (Int.natAbs_pos.mpr hσ)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg K Ω A v h _ hm
  have hW1 : IsOpen ((U0 : Set (Dec (F := K) A)) ∩ {d | (d : G K Ω) ζ = ζ}) := by
    refine U0.isOpen.inter ?_
    have := (stabilizer_isOpen_of_isIntegral (K := K) ζ).preimage
      (continuous_subtype_val (p := fun x => x ∈ Dec (F := K) A))
    convert this using 1
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW1
    ⟨U0.toSubgroup.one_mem, AlgEquiv.one_apply ζ⟩
  haveI : U.toSubgroup.Normal := U.isNormal'

  have hdense : ∀ d : Dec (F := K) A, ∃ w : Weil h, ∃ u ∈ U.toSubgroup, d = ι w * u := by
    intro d
    have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine K Ω A v h (ι (frob h)) (isFrob_frob (h := h))
    have h2 : Subgroup.zpowers (ι (frob h)) ⊔ (Ine (F := K) A).subgroupOf (Dec (F := K) A) ≤ ι.range := by
      refine sup_le ?_ fun x hx => ⟨⟨x, Ine_le_Weil h hx⟩, rfl⟩
      rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    have hd : Dense (ι.range : Set (Dec (F := K) A)) := by
      intro x
      have hx : x ∈ (⊤ : Subgroup (Dec (F := K) A)) := trivial
      rw [← h1] at hx
      exact closure_mono h2 hx
    have hopen : IsOpen {x : Dec (F := K) A | d⁻¹ * x ∈ U.toSubgroup} :=
      U.isOpen.preimage (continuous_const_mul d⁻¹)
    obtain ⟨x, hxU, w, rfl⟩ := hd.inter_open_nonempty _ hopen ⟨d, by simp⟩
    exact ⟨w, (d⁻¹ * ι w)⁻¹, U.toSubgroup.inv_mem hxU, by group⟩
  have hJW : ∀ (w : Weil h) (j : Dec (F := K) A), j ∈ J → ι w * j * (ι w)⁻¹ ∈ J := by
    rintro w j ⟨hjI, hjρ⟩
    refine ⟨conj_mem_Ine (Weil_le_Dec h w.2) hjI, fun hw => ?_⟩
    exact hconj w ⟨j, Ine_le_Weil h hjI⟩ (hjρ _)
  have hU0J : ∀ d : Dec (F := K) A, d ∈ U0.toSubgroup → (d : G K Ω) ∈ Ine (F := K) A → d ∈ J :=
    fun d hd hI => hPW d (hU0 hd) hI
  have hUU0 : ∀ d : Dec (F := K) A, d ∈ U.toSubgroup → d ∈ U0.toSubgroup := fun d hd => (hU hd).1
  have hUζ : ∀ d : Dec (F := K) A, d ∈ U.toSubgroup → (d : G K Ω) ζ = ζ := fun d hd => (hU hd).2
  have hJI : ∀ j ∈ J, (j : G K Ω) ∈ Ine (F := K) A := fun j hj => hj.1
  haveI hJn : J.Normal := ⟨fun j hj d => by
    obtain ⟨w, u, hu, rfl⟩ := hdense d
    have h1 : u * j * u⁻¹ ∈ J := by
      have hc : u * j * u⁻¹ * j⁻¹ ∈ J := by
        refine hU0J _ (hUU0 _ ?_) ?_
        · have h3 : j * u⁻¹ * j⁻¹ ∈ U.toSubgroup :=
            (inferInstance : U.toSubgroup.Normal).conj_mem _ (U.toSubgroup.inv_mem hu) j
          have h4 := U.toSubgroup.mul_mem hu h3
          have e : u * (j * u⁻¹ * j⁻¹) = u * j * u⁻¹ * j⁻¹ := by group
          rwa [e] at h4
        · exact (Ine (F := K) A).mul_mem (conj_mem_Ine u.2 (hJI j hj)) ((Ine (F := K) A).inv_mem (hJI j hj))
      have h5 := J.mul_mem hc hj
      have e : u * j * u⁻¹ * j⁻¹ * j = u * j * u⁻¹ := by group
      rwa [e] at h5
    have h6 := hJW w _ h1
    have e : ι w * (u * j * u⁻¹) * (ι w)⁻¹ = ι w * u * j * (ι w * u)⁻¹ := by group
    rwa [e] at h6⟩
  let N : Subgroup (Dec (F := K) A) := J ⊔ U.toSubgroup
  have hNmem : ∀ x ∈ N, ∃ j ∈ J, ∃ u ∈ U.toSubgroup, j * u = x := by
    intro x hx
    have h1 : x ∈ ((J ⊔ U.toSubgroup : Subgroup _) : Set (Dec (F := K) A)) := hx
    rw [Subgroup.mul_normal] at h1
    obtain ⟨j, hj, u, hu, e⟩ := h1
    exact ⟨j, hj, u, hu, e⟩
  haveI hNn : N.Normal := Subgroup.sup_normal J U.toSubgroup
  have hk : ∀ x ∈ N, QuotientGroup.mk' N x = 1 := fun x hx => by
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have hcN : commutator (Dec (F := K) A) ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro d1 _ d2 _
    obtain ⟨w1, u1, hu1, rfl⟩ := hdense d1
    obtain ⟨w2, u2, hu2, rfl⟩ := hdense d2
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    rw [map_commutatorElement, map_mul, map_mul, hk u1 (Subgroup.mem_sup_right hu1),
      hk u2 (Subgroup.mem_sup_right hu2), mul_one, mul_one, ← map_commutatorElement,
      ← map_commutatorElement]
    apply hk
    apply Subgroup.mem_sup_left
    rw [commutatorElement_def]
    have hd0 : deg (w1 * w2 * w1⁻¹ * w2⁻¹) = 0 := by
      rw [deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]; ring
    exact ⟨deg_eq_zero_iff.mp hd0, fun _ => hcomm w1 w2⟩

  refine ⟨Subgroup.zpowers (ι σ) ⊔ N, ?_, le_trans hcN le_sup_right,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers (ι σ)), ?_⟩
  · exact Subgroup.isOpen_mono (le_trans (le_sup_right : U.toSubgroup ≤ N) le_sup_right) U.isOpen
  intro τ g hg hgτ
  have hgI : (g : G K Ω) ∈ Ine (F := K) A := hgτ ▸ τ.2
  have hg' : g ∈ ((Subgroup.zpowers (ι σ) ⊔ N : Subgroup _) : Set (Dec (F := K) A)) := hg
  rw [Subgroup.mul_normal] at hg'
  obtain ⟨s, hs, x, hx, rfl⟩ := hg'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  obtain ⟨j, hj, u, hu, rfl⟩ := hNmem x hx
  have hkW : ((ι σ ^ k : Dec (F := K) A) : G K Ω) ∈ Weil h := by
    rw [Subgroup.coe_zpow]; exact zpow_mem σ.2 k
  have huW : (u : G K Ω) ∈ Weil h := by
    have e : u = (ι σ ^ k * j)⁻¹ * (ι σ ^ k * (j * u)) := by group
    rw [e]
    exact (Weil h).mul_mem ((Weil h).inv_mem ((Weil h).mul_mem hkW (Ine_le_Weil h (hJI j hj))))
      (Ine_le_Weil h hgI)
  have hdeg : deg (⟨(u : G K Ω), huW⟩ : Weil h) = -(k * deg σ) := by
    have e : (⟨((ι σ ^ k * (j * u) : Dec (F := K) A) : G K Ω), Ine_le_Weil h hgI⟩ : Weil h) =
        σ ^ k * (⟨(j : G K Ω), Ine_le_Weil h (hJI j hj)⟩ * ⟨(u : G K Ω), huW⟩) := by
      apply Subtype.ext
      simp [Subgroup.coe_zpow, ι]
    have h0 := (deg_eq_zero_iff (σ := ⟨_, Ine_le_Weil h hgI⟩)).mpr hgI
    rw [e, deg_mul, deg_mul, deg_zpow,
      (deg_eq_zero_iff (σ := ⟨_, Ine_le_Weil h (hJI j hj)⟩)).mpr (hJI j hj)] at h0
    linarith
  have hnk : (n : ℤ) ∣ k := by
    have h1 := hζ ⟨(u : G K Ω), huW⟩ (hUζ u hu)
    rw [hdeg, dvd_neg, Nat.cast_mul, Int.natCast_natAbs,
      show (n : ℤ) * |deg σ| = |(n : ℤ) * deg σ| by rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg n)],
      abs_dvd] at h1
    exact (mul_dvd_mul_iff_right hσ).mp h1
  obtain ⟨t, ht⟩ := hnk
  have hk0 : ι σ ^ k ∈ U0.toSubgroup := by
    rw [ht, zpow_mul, zpow_natCast]; exact U0.toSubgroup.zpow_mem hσn t
  have hgJ : ι σ ^ k * (j * u) ∈ J := by
    have hj' : ι σ ^ k * j * (ι σ ^ k)⁻¹ ∈ J := by
      have h1 := hJW (σ ^ k) j hj
      rwa [map_zpow] at h1
    have hc0 : ι σ ^ k * u ∈ U0.toSubgroup := U0.toSubgroup.mul_mem hk0 (hUU0 u hu)
    have hcI : ((ι σ ^ k * u : Dec (F := K) A) : G K Ω) ∈ Ine (F := K) A := by
      have e2 : ι σ ^ k * u = (ι σ ^ k * j * (ι σ ^ k)⁻¹)⁻¹ * (ι σ ^ k * (j * u)) := by group
      rw [e2]
      exact (Ine (F := K) A).mul_mem ((Ine (F := K) A).inv_mem (hJI _ hj')) hgI
    have e : ι σ ^ k * (j * u) = (ι σ ^ k * j * (ι σ ^ k)⁻¹) * (ι σ ^ k * u) := by group
    rw [e]
    exact J.mul_mem hj' (hU0J _ hc0 hcI)
  obtain ⟨hgI', hgρ⟩ := hgJ
  rw [WD.charPol_mk, WD.lpDim_mk]
  have e : ineIncl h τ = ⟨((ι σ ^ k * (j * u) : Dec (F := K) A) : G K Ω), Ine_le_Weil h hgI'⟩ :=
    Subtype.ext hgτ.symm
  rw [e, hgρ, LinearMap.charpoly_one]

end GlobalTheory.AboveL.AbSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRep
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.Cong

theorem exists_weight_of_isAutRepU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ)
    (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∃ lam : (E →+* ℂ) → DomWeight a, ∀ τ, HasWeightAt U τ (lam τ) := by
  intro E _ _ _ a U hU
  choose lam hlam using fun τ : E →+* ℂ => (GlobalTheory.DefU.AU.existsUnique_hasWt E a (GlobalTheory.DefU.AU.mk ⟨U, hU⟩) τ).exists
  exact ⟨lam, hlam⟩

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOver
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

private theorem coe_le_one {L Ω : Type} [Field Ω] [Field L] [NumberField L] [Algebra L Ω]
    (A : ValuationSubring Ω) (c : 𝓞 L) : A.valuation (algebraMap L Ω (c : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap L Ω) c.isIntegral_coe))

theorem exists_isPlaceOver_of_tower : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → ∃ v' : HeightOneSpectrum (𝓞 L), IsPlaceOver A v' ∧ v'.under (𝓞 K) = v := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v h
  let m : Ideal (𝓞 L) :=
    { carrier := {y | A.valuation (algebraMap L Ω (y : L)) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _)] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c y hy
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hy ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (coe_le_one A c)) hy }
  have hmem : ∀ y : 𝓞 L, y ∈ m ↔ A.valuation (algebraMap L Ω (y : L)) < 1 := fun y => Iff.rfl
  have hprime : m.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]; simp
    · intro x y hxy
      rw [hmem, hmem] at *
      have e : ((x * y : 𝓞 L) : L) = (x : L) * y := rfl
      rw [e, map_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      exact absurd hxy (not_lt.mpr (one_le_mul hc.1 hc.2))
  have hK : ∀ x : 𝓞 K, (algebraMap (𝓞 K) (𝓞 L) x ∈ m ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hmem, ← h x]
    have : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
      have e : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
      rw [e, ← IsScalarTower.algebraMap_apply]
    rw [this]
  have hne : m ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 K) (𝓞 L) x ∈ m := (hK x).mpr hx
    rw [hb, Ideal.mem_bot] at h1
    apply hx0
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)) (by rw [h1, map_zero])
  refine ⟨⟨m, hprime, hne⟩, ?_, ?_⟩
  · intro y
    exact (hmem y).symm.trans Iff.rfl
  · apply HeightOneSpectrum.ext
    ext x
    exact hK x

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResDeg

theorem normV_eq_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ w
  refine ⟨w.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

end GlobalTheory.AboveL.ResDeg
end

