module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0037
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterInfinityType
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeArch

open InfinitePlace.Completion

variable {E : Type} [Field E] [NumberField E]

theorem infiniteEmbedding_eq (w : InfinitePlace E) (a : (w.Completion)ˣ) :
    (infiniteEmbedding w a : IdeleGroup E) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w a := by
  classical
  refine Units.ext (Prod.ext ?_ rfl)
  show Pi.mulSingle w (a : w.Completion) = Pi.mulSingle w (a : w.Completion)
  congr!

theorem component_on_field (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) (k : Eˣ) :
    (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) (Formalism.L2.Host.atInf _ k) : Circle) : ℂ) =
      (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ n i := by
  have h := (GlobalTheory.InfTypeLocal.infType_iff_local E I φ hφ χ.1 χ.2.1 n).1 hn i k
  rw [HeckeCharacter.infiniteComponent_apply, coe_toIdele, infiniteEmbedding_eq]
  exact h

theorem denseRange_atInf_place (w : InfinitePlace E) : DenseRange (Formalism.L2.Host.atInf w) :=
  ((Function.surjective_eval w).denseRange.comp (GlobalTheory.InfTypeLocal.denseRange_atInf E)
    (continuous_apply w) : DenseRange _)

theorem component_eq (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I)
    (e : (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hec : Continuous e)
    (he : ∀ k : E, e (algebraMap E _ k) = φ i k) (a : ((InfinitePlace.mk (φ i)).Completion)ˣ) :
    (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) a : Circle) : ℂ) =
      (e a / ((‖e a‖ : ℝ) : ℂ)) ^ n i := by
  have h1 : Continuous fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ => e u :=
    hec.comp Units.continuous_val
  have h2 : ∀ u : ((InfinitePlace.mk (φ i)).Completion)ˣ, e u ≠ 0 := fun u =>
    (map_ne_zero _).2 u.ne_zero
  have h3 : ∀ u : ((InfinitePlace.mk (φ i)).Completion)ˣ, ((‖e u‖ : ℝ) : ℂ) ≠ 0 := fun u => by
    exact_mod_cast norm_ne_zero_iff.2 (h2 u)
  have key : (fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ =>
      (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) u : Circle) : ℂ)) =
      fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ => (e u / ((‖e u‖ : ℝ) : ℂ)) ^ n i := by
    refine (denseRange_atInf_place _).equalizer ?_ ?_ ?_
    · exact continuous_subtype_val.comp (map_continuous _)
    · exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _
        fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
    · funext k
      show _ = (e (algebraMap E _ (k : E)) / ((‖e (algebraMap E _ (k : E))‖ : ℝ) : ℂ)) ^ n i
      rw [he]
      exact component_on_field χ hu hφ n hn i k
  exact congrFun key a

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    (starRingEnd ℂ) z / ((‖z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [inv_div, div_eq_div_iff h0 hz, Complex.conj_mul']
  ring

theorem params (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) (hc : (InfinitePlace.mk (φ i)).IsComplex) :
    (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧
      ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  set w := InfinitePlace.mk (φ i) with hw
  set T := toHecke χ hu with hT
  have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hc
  set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc with he
  have hec : Continuous e.symm := (isometryEquivComplexOfIsComplex hc).symm.continuous
  set ψ : ℂˣ →ₜ* Circle := (T.infiniteComponent w).comp (unitsContinuousHom e.symm hec) with hψ
  obtain ⟨p, -, huniq⟩ := existsUnique_complexUnits_circle ψ
  have hι : ∀ z : ℂˣ, extensionEmbedding w ((unitsContinuousHom e.symm hec z : (w.Completion)ˣ) : w.Completion) = z :=
    fun z => e.apply_symm_apply (z : ℂ)
  have hnorm : ∀ z : ℂˣ, ‖((unitsContinuousHom e.symm hec z : (w.Completion)ˣ) : w.Completion)‖ = ‖(z : ℂ)‖ := fun z => by
    rw [← hι z]
    exact ((isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm
  have h1 : ∀ z : ℂˣ, (ψ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (T.infiniteWeight w, 2 * T.infiniteTau w).1 *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((((T.infiniteWeight w, 2 * T.infiniteTau w).2 : ℝ) : ℂ) * Complex.I) := fun z => by
    have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
    show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
    rw [HeckeCharacter.infiniteComponent_eq, hι, hnorm, InfinitePlace.mult, if_neg hnr,
      ofReal_pow_cpow hpos]
    congr 2
    push_cast
    ring
  have h2 : ∃ s : ℤ, s.natAbs = (n i).natAbs ∧ ∀ z : ℂˣ, (ψ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (s, (0 : ℝ)).1 *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((((s, (0 : ℝ)).2 : ℝ) : ℂ) * Complex.I) := by
    have h0 : ∀ k : E, extensionEmbedding w (algebraMap E _ k) = w.embedding k := fun k => by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply, extensionEmbedding_coe]
      rfl
    have hcont := (isometry_extensionEmbedding w).continuous
    rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
    · refine ⟨n i, rfl, fun z => ?_⟩
      have := component_eq χ hu hφ n hn i (extensionEmbedding w) hcont
        (fun k => by rw [h0, hw, h]) (unitsContinuousHom e.symm hec z)
      show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
      rw [this, hι]
      simp
    · refine ⟨-n i, by simp, fun z => ?_⟩
      have := component_eq χ hu hφ n hn i ((starRingEnd ℂ).comp (extensionEmbedding w))
        (Complex.continuous_conj.comp hcont)
        (fun k => by
          rw [RingHom.comp_apply, h0, hw, h]
          simp) (unitsContinuousHom e.symm hec z)
      show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
      rw [this, RingHom.comp_apply, hι, Complex.norm_conj, conj_div_norm z.ne_zero, inv_zpow, ← zpow_neg]
      simp
  obtain ⟨s, hs, h2⟩ := h2
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have e3 := e1.trans e2.symm
  have e4 : T.infiniteWeight w = s := congrArg Prod.fst e3
  have e5 : 2 * T.infiniteTau w = 0 := congrArg Prod.snd e3
  exact ⟨by linarith, by rw [e4, hs]⟩

theorem infiniteParams_of_hasInf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → ∀ i : I, (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  intro E _ _ _ I _ φ hφ χ hu n hn i
  exact params χ hu (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ) n hn i
    (IsTotallyComplex.isComplex _)

end GlobalTheory.CompanionTheory.HeckeArch
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterNotNormPower
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section
namespace GlobalTheory.CompanionTheory.HeckeBridge.NotPow

open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (atInf)

theorem exists_ext_surj {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (hw : (InfinitePlace.mk φ).IsComplex) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧ (∀ k : L, e (algebraMap L _ k) = φ k) ∧
      Function.Surjective e ∧ ∀ x, ‖e x‖ = ‖x‖ := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_,
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw, fun x => ?_⟩
    · rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe, h]
      rfl
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _) x
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_, fun y => ?_, fun x => ?_⟩
    · rw [RingHom.comp_apply, InfinitePlace.Completion.algebraMap_apply,
        InfinitePlace.Completion.extensionEmbedding_coe, h, ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_conj _
    · obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw
        ((starRingEnd ℂ) y)
      exact ⟨x, by rw [RingHom.comp_apply, hx, Complex.conj_conj]⟩
    · rw [RingHom.comp_apply, Complex.norm_conj]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _) x

theorem exists_norm_one_zpow_ne (m : ℤ) (hm : m ≠ 0) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ ^ m ≠ 1 := by
  refine ⟨Complex.exp (((Real.pi / m : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_int_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hx : (m : ℂ) * (((Real.pi / m : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hx, Complex.exp_pi_mul_I]
  norm_num

private theorem exists_inclusion_mul_eq_mul_inclusion_of_normal {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ c : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous c ∧ ∀ k : L, c (algebraMap L _ k) = φ k := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_⟩
    rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe, h]
    rfl
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_⟩
    rw [RingHom.comp_apply, InfinitePlace.Completion.algebraMap_apply,
      InfinitePlace.Completion.extensionEmbedding_coe, h, ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_conj _

private theorem denseRange_units_map_infiniteAdeleRing (E : Type) [Field E] [NumberField E] :
    DenseRange (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom) := by
  have hopen : IsOpenMap (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
    Units.isOpenMap_val (R := (w : InfinitePlace E) → w.Completion)
  have hd := InfiniteAdeleRing.denseRange_algebraMap E
  rw [DenseRange, dense_iff_inter_open]
  rintro V hV ⟨u, hu⟩
  obtain ⟨_, ⟨u', hu', rfl⟩, k, hk⟩ := hd.inter_open_nonempty _ (hopen V hV) ⟨u, u, hu, rfl⟩
  by_cases hk0 : k = 0
  · have h0 : (u' : InfiniteAdeleRing E) = 0 := by rw [← hk, hk0, map_zero]
    have h01 : (0 : InfiniteAdeleRing E) = 1 := by rw [← u'.mul_inv, h0, zero_mul]
    haveI := subsingleton_of_zero_eq_one h01
    exact ⟨u', hu', 1, Units.ext (Subsingleton.elim _ _)⟩
  · exact ⟨u', hu', Units.mk0 k hk0, Units.ext (by simpa using hk)⟩

theorem comp_eq {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hb : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar E) {n : I → ℤ}
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I)
    (e : (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hec : Continuous e)
    (he : ∀ k : E, e (algebraMap E _ k) = φ i k) (z : ((InfinitePlace.mk (φ i)).Completion)ˣ) :
    ((χ.1 (infIdele E _ z) : ℂˣ) : ℂ) =
      (e (z : (InfinitePlace.mk (φ i)).Completion) /
        ((‖e (z : (InfinitePlace.mk (φ i)).Completion)‖ : ℝ) : ℂ)) ^ n i := by
  classical
  choose c₀ hc₀ hc₀' using fun j => exists_inclusion_mul_eq_mul_inclusion_of_normal (φ j)
  let c : ∀ j, (InfinitePlace.mk (φ j)).Completion →+* ℂ := Function.update c₀ i e
  have hc : ∀ j, Continuous (c j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa [c] using hec
    · simpa [c, hj] using hc₀ j
  have hc' : ∀ j (k : E), c j (algebraMap E _ k) = φ j k := by
    intro j k
    by_cases hj : j = i
    · subst hj
      simpa [c] using he k
    · simpa [c, hj] using hc₀' j k
  let ι0 : InfiniteAdeleRing E →* NumberField.AdeleRing (NumberField.RingOfIntegers E) E :=
    MonoidHom.inl (InfiniteAdeleRing E) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers E) E)
  have hι0 : Continuous ι0 := continuous_id.prodMk continuous_const
  obtain ⟨hχc, -⟩ := χ.2
  let Ψ : (InfiniteAdeleRing E)ˣ → ℂ := fun u => ((χ.1 (Units.map ι0 u) : ℂˣ) : ℂ)
  let Θ : (InfiniteAdeleRing E)ˣ → ℂ := fun u => ∏ j, (c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) /
      ((‖c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ^ n j
  have hne : ∀ (j : I) (u : (InfiniteAdeleRing E)ˣ),
      c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) ≠ 0 := by
    intro j u h0
    have h1 := congrArg (fun x : InfiniteAdeleRing E => x (InfinitePlace.mk (φ j))) u.mul_inv
    have h2 : (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) = 0 := (map_eq_zero (c j)).1 h0
    change (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) *
      ((u⁻¹ : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) = 1 at h1
    rw [h2, zero_mul] at h1
    exact zero_ne_one h1
  have hΨ : Continuous Ψ := Units.continuous_val.comp (hχc.comp (Continuous.units_map ι0 hι0))
  have hΘ : Continuous Θ := by
    refine continuous_finsetProd _ fun j _ => ?_
    have hcont : Continuous fun u : (InfiniteAdeleRing E)ˣ =>
        c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) :=
      (hc j).comp ((continuous_apply (InfinitePlace.mk (φ j))).comp Units.continuous_val)
    have hn0 : ∀ u : (InfiniteAdeleRing E)ˣ,
        (((‖c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ≠ 0 :=
      fun u => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne j u))
    exact (hcont.div (Complex.continuous_ofReal.comp (continuous_norm.comp hcont)) hn0).zpow₀ (n j)
      fun u => Or.inl (div_ne_zero (hne j u) (hn0 u))
  have hkey : Ψ = Θ := by
    refine Continuous.ext_on (denseRange_units_map_infiniteAdeleRing E) hΨ hΘ ?_
    rintro _ ⟨k, rfl⟩
    have hdiag : Units.map ι0 (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) =
        Formalism.L2.Host.infDiag k := by
      apply Units.ext
      simp only [Formalism.L2.Host.infDiag, MonoidHom.coe_finsetProd, Finset.prod_apply, MonoidHom.coe_comp,
        Function.comp_apply, Units.coe_prod, Units.coe_map]
      have hprod : (∏ w, (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) w
          (algebraMap E w.Completion (k : E)) : InfiniteAdeleRing E)) = algebraMap E (InfiniteAdeleRing E) (k : E) :=
        Finset.univ_prod_mulSingle (fun w : InfinitePlace E => algebraMap E w.Completion (k : E))
      rw [Finset.prod_congr rfl fun w _ => (show ((infIdele E w (Formalism.L2.Host.atInf w k) : Neutral.B1.Ideles E) :
          NumberField.AdeleRing (NumberField.RingOfIntegers E) E) =
          ι0 (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) w (algebraMap E w.Completion (k : E))) from rfl)]
      exact (congrArg ι0 hprod.symm).trans (map_prod ι0 _ _)
    have hinf := hn k
    simp only [Formalism.L2.Host.HChar.inf, MonoidHom.coe_comp, Function.comp_apply] at hinf
    show ((χ.1 (Units.map ι0 (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k)) : ℂˣ) : ℂ) = _
    rw [hdiag]
    refine hinf.trans (Finset.prod_congr rfl fun j _ => ?_)
    show _ = (c j (algebraMap E _ (k : E)) / ((‖c j (algebraMap E _ (k : E))‖ : ℝ) : ℂ)) ^ n j
    rw [hc' j]
  have hz := congrFun hkey
    (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) (InfinitePlace.mk (φ i))) z)
  have hι : Units.map ι0
      (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) (InfinitePlace.mk (φ i))) z) =
      infIdele E _ z := by
    apply Units.ext
    rfl
  simp only [Ψ, Θ] at hz
  rw [hι] at hz
  let a : ∀ w : InfinitePlace E, w.Completion :=
    Pi.mulSingle (InfinitePlace.mk (φ i)) (z : (InfinitePlace.mk (φ i)).Completion)
  change _ = ∏ j, (c j (a (InfinitePlace.mk (φ j))) /
      ((‖c j (a (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ^ n j at hz
  rw [hz, Finset.prod_eq_single i]
  · simp [a, c]
  · intro j _ hj
    have hw : InfinitePlace.mk (φ j) ≠ InfinitePlace.mk (φ i) := fun h => hj (hb.1 h)
    simp [a, Pi.mulSingle_eq_of_ne hw]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ideleModule_infIdele {E : Type} [Field E] [NumberField E] (w : InfinitePlace E)
    (z : (w.Completion)ˣ) :
    (ideleModule E (infIdele E w z) : ℝ) = ‖(z : w.Completion)‖ ^ w.mult := by
  classical
  show (IdeleGroup.infiniteModule (infIdele E w z) * IdeleGroup.finiteModule (infIdele E w z) : ℝ) = _
  have hinf : IdeleGroup.infiniteModule (infIdele E w z : IdeleGroup E) = ‖(z : w.Completion)‖ ^ w.mult := by
    unfold IdeleGroup.infiniteModule
    rw [Fintype.prod_eq_single w]
    · show ‖(Pi.mulSingle w (z : w.Completion) : ∀ w', w'.Completion) w‖ ^ w.mult = _
      rw [Pi.mulSingle_eq_same]
    · intro w' hw'
      show ‖(Pi.mulSingle w (z : w.Completion) : ∀ w', w'.Completion) w'‖ ^ w'.mult = 1
      rw [Pi.mulSingle_eq_of_ne hw', norm_one, one_pow]
  have hfin : IdeleGroup.finiteModule (infIdele E w z : IdeleGroup E) = 1 := by
    unfold IdeleGroup.finiteModule
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    show ‖(1 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers E) E) v‖ = 1
    simp
  rw [hinf, hfin, mul_one]

theorem not_modulePow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, ((toHecke χ hu).toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  intro E _ _ _ I _ φ hcm χ hu n hn hex hτex
  obtain ⟨i, hi⟩ := hex
  obtain ⟨τ, hτ⟩ := hτex
  have hb := GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hcm
  have hw : (InfinitePlace.mk (φ i)).IsComplex := IsTotallyComplex.isComplex _
  obtain ⟨e, hec, he, hes, hen⟩ := exists_ext_surj (φ i) hw
  obtain ⟨ζ, hζ1, hζm⟩ := exists_norm_one_zpow_ne (n i) hi
  obtain ⟨y, rfl⟩ := hes ζ
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hy1 : ‖y‖ = 1 := by rw [← hen]; exact hζ1
  have h3 := comp_eq hb χ hn i e hec he (Units.mk0 y hy0)
  have h4 := ideleModule_infIdele (InfinitePlace.mk (φ i)) (Units.mk0 y hy0)
  have h5 := hτ (infIdele E _ (Units.mk0 y hy0))
  rw [GlobalTheory.CompanionTheory.HeckeBridge.coe_toIdele] at h5
  apply hζm
  simp only [Units.val_mk0] at h3 h4
  rw [hζ1, Complex.ofReal_one, div_one] at h3
  rw [← h3]
  refine h5.trans ?_
  rw [h4, hy1, one_pow, Complex.ofReal_one, Complex.one_cpow]

end GlobalTheory.CompanionTheory.HeckeBridge.NotPow
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeCharacterConductorExponent
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

theorem comp_finiteUnitsSingle (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) :
    (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)) =
      ((toHecke χ hu).localComponent v : (v.adicCompletion E)ˣ →* Circle) := by
  refine MonoidHom.ext fun a => ?_
  show (toHecke χ hu).toIdele (ofFinite (finiteUnitsSingle v a)) = (toHecke χ hu).localComponent v a
  rw [GroundTheory.Global.IdeleGroup.ofFinite_finiteUnitsSingle, GroundTheory.Global.HeckeCharacter.localComponent_apply]

private theorem toHecke_local_eq_one_iff (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) :
    (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)) x = 1 ↔ χ.loc v x = 1 := by
  rw [comp_finiteUnitsSingle χ hu v]
  have h := coe_localComponent χ hu v x
  constructor
  · intro h1
    apply Units.ext
    rw [← h]
    have h1' : (toHecke χ hu).localComponent v x = 1 := h1
    rw [h1', Circle.coe_one, Units.val_one]
  · intro h1
    have h1' : (toHecke χ hu).localComponent v x = 1 := by
      apply Circle.ext
      rw [h, h1, Units.val_one, Circle.coe_one]
    exact h1'

theorem levelLe_iff_unitsLevel_le_ker (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔
      unitsLevel v n ≤ (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)).ker := by
  unfold Formalism.L2.Host.HChar.LevelLe
  constructor
  · intro h x hx
    rw [GroundTheory.Global.mem_unitsLevel] at hx
    rw [MonoidHom.mem_ker, toHecke_local_eq_one_iff χ hu v x]
    exact h x hx.1 hx.2
  · intro h x hux hx
    rw [← toHecke_local_eq_one_iff χ hu v x]
    exact h (GroundTheory.Global.mem_unitsLevel.mpr ⟨hux, hx⟩)

theorem levelLe_iff_conductorExponentAt (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) v ≤ n := by
  rw [levelLe_iff_unitsLevel_le_ker χ hu v n]
  exact GroundTheory.Global.unitsLevel_le_ker_iff v GroundTheory.Global.Circle.noSmallSubgroups _
    (((toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite).comp
      (GroundTheory.Global.IdeleGroup.continuous_finiteUnitsSingle v))

private theorem asIdeal_pow_dvd_finprod_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    {a : HeightOneSpectrum R → ℕ} (ha : (Function.support a).Finite) (v : HeightOneSpectrum R) (k : ℕ) :
    v.asIdeal ^ k ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w ↔ k ≤ a v := by
  classical
  have hfin : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ a w).Finite := by
    rw [GroundTheory.Global.mulSupport_asIdeal_pow]; exact ha
  constructor
  · intro hk
    by_contra hlt
    rw [not_le] at hlt
    set b : HeightOneSpectrum R → ℕ := Function.update a v 0 with hb
    have hbfin : (Function.support b).Finite := by
      refine ha.subset (fun w hw => ?_)
      by_cases hwv : w = v
      · subst hwv
        simp [hb] at hw
      · simpa [hb, Function.update_of_ne hwv] using hw
    have hcfin : (Function.mulSupport fun w : HeightOneSpectrum R =>
        w.asIdeal ^ (if w = v then a v else 0)).Finite := by
      refine (Set.finite_singleton v).subset (fun w hw => ?_)
      rw [Set.mem_singleton_iff]
      by_contra hwv
      exact hw (by simp [hwv])
    have hbfin' : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ b w).Finite := by
      rw [GroundTheory.Global.mulSupport_asIdeal_pow]; exact hbfin
    have hsingle : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ (if w = v then a v else 0) = v.asIdeal ^ a v := by
      rw [finprod_eq_single _ v (fun w hw => by simp [hw])]
      simp
    have hsplit : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w =
        v.asIdeal ^ a v * ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w := by
      rw [← hsingle, ← finprod_mul_distrib hcfin hbfin']
      refine finprod_congr fun w => ?_
      by_cases hwv : w = v
      · subst hwv
        simp [hb]
      · simp [hb, hwv, Function.update_of_ne hwv]
    rw [hsplit] at hk
    have hpow : v.asIdeal ^ k = v.asIdeal ^ a v * v.asIdeal ^ (k - a v) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow] at hk
    have hne0 : v.asIdeal ^ a v ≠ 0 := pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
    have hk' := (mul_dvd_mul_iff_left hne0).mp hk
    have hv : v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w :=
      (dvd_pow_self _ (by omega)).trans hk'
    have h1 := (GroundTheory.Global.asIdeal_dvd_finprod_iff hbfin v).mp hv
    simp [hb] at h1
  · intro hk
    exact (pow_dvd_pow _ hk).trans
      (finprod_mem_dvd (f := fun w : HeightOneSpectrum R => w.asIdeal ^ a w) v hfin)

theorem multiplicity_conductor_toHecke (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ)
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (h : ExpAt χ v m) :
    multiplicity v.asIdeal (toHecke χ hu).conductor = m := by
  have hcont : Continuous ((toHecke χ hu).toIdele.comp ofFinite) :=
    (toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite
  have hfin := GroundTheory.Global.IdeleGroup.finite_support_conductorExponentAt
    GroundTheory.Global.Circle.noSmallSubgroups _ hcont
  have hne := (toHecke χ hu).conductor_ne_bot
  have hcond : χ.IsCond (toHecke χ hu).conductor := by
    unfold Formalism.L2.Host.HChar.IsCond
    refine ⟨hne, fun w n => ?_⟩
    rw [levelLe_iff_conductorExponentAt χ hu w n]
    have h1 := asIdeal_pow_dvd_finprod_iff hfin w (n + 1)
    change _ ↔ ¬ w.asIdeal ^ (n + 1) ∣ ∏ᶠ u : HeightOneSpectrum (𝓞 E),
      u.asIdeal ^ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) u
    rw [h1]
    constructor <;> intro h2 <;> omega
  exact (GlobalTheory.CMVal.ExpAt.unique h ((GlobalTheory.CMVal.isCond_iff_expAt χ hne).mp hcond v)).symm

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

