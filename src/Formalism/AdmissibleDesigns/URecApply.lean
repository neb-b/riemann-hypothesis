module

public import Formalism.AdmissibleDesigns.Bundle0009
public import Formalism.AdmissibleDesigns.H1MapMemLcH1
public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.AdmissibleDesigns.Bundle0004

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

def CycW : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (g : Dw i dc (idx i dc w)),
    (((Br.PD D.loc D.nbr i w hw).χ (eW i dc hw g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      (((cycE i (g : GE D.nd) : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) : ℚ_[D.nd.l i])

def sE (e : ℕ) (g : GE D.nd) : D.nd.O i :=
  ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp (cycE i ^ (-(e : ℤ)))) g : (D.nd.O i)ˣ) : D.nd.O i)

def epsL {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) : Br.Ow (D.nbr i w hw) :=
  (D.nbr i w hw).eO (algebraMap ℤ_[D.nd.l i] (D.nd.O i) (((cycE i ((eW i dc hw).symm h : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]))

end Rec

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem algZ_LL {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (z : ℤ_[D.nd.l i]) :
    algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) ((D.nbr i w hw).eO (algebraMap ℤ_[D.nd.l i] (D.nd.O i) z)) =
      algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw)) (z : ℚ_[D.nd.l i]) := by
  rw [(D.nbr i w hw).eO_alg z, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[D.nd.l i] ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw))]
  rfl

theorem epsL_eq (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) :
    algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h) =
      algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw))
        ((((Br.PD D.loc D.nbr i w hw).χ h)⁻¹ : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) := by
  have hc := hcyc w hw ((eW i dc hw).symm h)
  rw [MulEquiv.apply_symm_apply] at hc
  rw [epsL, algZ_LL, Units.val_inv_eq_inv_val, hc]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one])

variable [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def uRec {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) :
    Mc i Dd c ≃+ ((Fin 1 → Br.LLw (D.nbr i w hw)) ⧸ Formalism.MainNotions.N.stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) 1) :=
  φ.toAddEquiv.trans (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw)) (fun c => Br.toLLK_alg (D.nbr i w hw) c))

theorem uRec_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (m : Mc i Dd c) :
    uRec i Dd hw c φ m =
      koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw)) (fun c => Br.toLLK_alg (D.nbr i w hw) c) (φ m) :=
  rfl

end Dict

section Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem yLoc_of
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (c : Fin (D.R.t + 1)) (n : ℕ) :
    YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc n) := by
  intro ψ _
  let _ := Formalism.MainNotions.N.K.Topo.fracTopology (D.nd.O i)
  let _ := Formalism.MainNotions.N.K.Topo.rTopology (D.nd.O i) Dd.R'
  have := Formalism.MainNotions.N.K.Topo.fracTop_addGroup_O i
  have := Formalism.MainNotions.N.K.Topo.fracTop_smul_O i
  have := Formalism.MainNotions.N.K.Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  have := Formalism.MainNotions.N.K.Topo.rTop_constSMul_RD i Dd
  have := Formalism.MainNotions.N.K.Topo.rTop_mul_RD i r π g0 eB e₁ s Dd hD
  have htors (m : Mc i Dd c) : ∃ a : D.nd.O i, a ≠ 0 ∧ a • m = 0 := by
    have h1 : ∀ y : KO (D.nd.O i), ∃ a : D.nd.O i, a ≠ 0 ∧ a • y = 0 := by
      intro y
      induction y using Submodule.Quotient.induction_on with
      | H x =>
        obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (D.nd.O i)) x
        refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
        exact ⟨a, by rw [Algebra.smul_def, mul_comm]; exact hab.symm⟩
    choose a ha0 ha using fun j => h1 (m j)
    refine ⟨∏ j, a j, Finset.prod_ne_zero_iff.2 fun j _ => ha0 j, ?_⟩
    funext j
    change (∏ j, a j) • m j = 0
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul, ha j, smul_zero]
  have hA := Formalism.MainNotions.N.K.Topo.fgTop_RD i r π g0 eB e₁ s Dd hD
  have hfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop (D.nd.O i) (Ymod Dd.r Dd.χ Dd.E) := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective ((Ymod Dd.r Dd.χ Dd.E).subtype.restrictScalars (D.nd.O i)) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : (D.nd.O i) × (Ymod Dd.r Dd.χ Dd.E) => q.1 • (q.2 : Dd.R'))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : D.nd.O i, a ≠ 0 ∧ ∀ y : Ymod Dd.r Dd.χ Dd.E, a • ψ y = 0 := by
    obtain ⟨t, ht⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Ymod Dd.r Dd.χ Dd.E => htors (ψ y)
    refine ⟨∏ y ∈ t, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span (D.nd.O i) (t : Set (Ymod Dd.r Dd.χ Dd.E)) := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem f hx
      rw [hb, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul b x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have continuous_of_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
      (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (φ : A →+* B)
      [IsLocalHom φ] : Continuous φ := by
    refine continuous_of_continuousAt_zero φ ?_
    rw [ContinuousAt, map_zero]
    intro s hs
    obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
    have hopen := (isAdic_iff.1 hA).1 n
    rw [Filter.mem_map]
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
    apply hn
    have hle : (IsLocalRing.maximalIdeal A).map φ ≤ IsLocalRing.maximalIdeal B :=
      Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit φ a ha
    have h1 : φ x ∈ ((IsLocalRing.maximalIdeal A) ^ n).map φ := Ideal.mem_map_of_mem φ hx
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle n h1
  
  have l_mem_max : ((D.nd.l i : ℕ) : D.nd.O i) ∈ IsLocalRing.maximalIdeal (D.nd.O i) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h2 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_unit D.nd D.naut i u
    have h3 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_l D.nd D.naut i
    rw [hu] at h2
    rw [h2] at h3
    exact lt_irrefl _ h3
  have l_ne_zero : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 :=
    Formalism.MainNotions.SumRepresentations.natCast_ne_zero_O D.nd i (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  have isLocalHom_alg : IsLocalHom (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    refine ⟨fun z hz => ?_⟩
    by_contra hn
    have h1 : z ∈ IsLocalRing.maximalIdeal ℤ_[D.nd.l i] := hn
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
    obtain ⟨y, rfl⟩ := h1
    rw [map_mul, map_natCast] at hz
    exact (IsLocalRing.mem_maximalIdeal _).1 (l_mem_max) (isUnit_of_mul_isUnit_left hz)
  have continuous_alg : Continuous (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    haveI := isLocalHom_alg
    exact continuous_of_isLocalHom (ReciprocityTheory.ChartRestriction.T2.padicCoeff_padicInt (p := D.nd.l i)).adic (D.nd.O_adic i) _
  have compact_O : CompactSpace (D.nd.O i) := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[D.nd.l i] (D.nd.O i)
    have hc : Continuous f := by
      have : (f : (Fin n → ℤ_[D.nd.l i]) → D.nd.O i) = fun v =>
          ∑ k, algebraMap ℤ_[D.nd.l i] (D.nd.O i) (v k) * f (fun j => if k = j then 1 else 0) := by
        funext v
        rw [LinearMap.pi_apply_eq_sum_univ f v]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Algebra.smul_def]
      rw [this]
      fun_prop (disch := exact continuous_alg)
    exact hf.compactSpace hc
  have t2Space_nd_O : T2Space (D.nd.O i) := by
    have hopen : ∀ n : ℕ, IsOpen ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) :=
      (isAdic_iff.1 (D.nd.O_adic i)).1
    have hclosed : ∀ n : ℕ, IsClosed ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) :=
      fun n => AddSubgroup.isClosed_of_isOpen (Submodule.toAddSubgroup (IsLocalRing.maximalIdeal (D.nd.O i) ^ n)) (hopen n)
    have h0 : ({0} : Set (D.nd.O i)) =
        ⋂ n : ℕ, ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
      constructor
      · rintro rfl n
        exact Ideal.zero_mem _
      · intro h
        have h1 : x ∈ (⨅ n : ℕ, IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) := by
          rw [Ideal.mem_iInf]; exact h
        rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top] at h1
        exact h1
    have : IsClosed ({0} : Set (D.nd.O i)) := by
      rw [h0]; exact isClosed_iInter hclosed
    haveI : T1Space (D.nd.O i) := IsTopologicalAddGroup.t1Space _ this
    infer_instance
  have padicCoeff_O : ReciprocityTheory.ChartRestriction.T2.PadicCoeff (D.nd.l i) (D.nd.O i) :=
    ⟨D.nd.trO i, compact_O, t2Space_nd_O, D.nd.O_adic i, l_mem_max, l_ne_zero⟩
  have hopen := hfg.isOpen_mulSub padicCoeff_O ha
  have hy : Continuous fun g => yY Dd.r Dd.χ Dd.E g :=
    Continuous.subtype_mk (f := fun g => (uElt Dd.r Dd.χ g - 1) * Dd.E)
      (((Formalism.MainNotions.N.K.Topo.uElt_cont i r π g0 eB e₁ s Dd hD hc).sub continuous_const).mul continuous_const) _
  set_option synthInstance.maxHeartbeats 200000 in
  have h : IsLocallyConstant fun g => ψ (yY Dd.r Dd.χ Dd.E g) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g₀
    refine ⟨(fun g => yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀) ⁻¹' _, hopen.preimage (hy.sub continuous_const), ?_, ?_⟩
    · show yY Dd.r Dd.χ Dd.E g₀ - yY Dd.r Dd.χ Dd.E g₀ ∈ Formalism.RepresentationBoundsCohomology.LOC.mulSub a (Ymod Dd.r Dd.χ Dd.E)
      rw [sub_self]
      exact zero_mem _
    · rintro g ⟨z, hz⟩
      have hz' : a • z = yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀ := hz
      have h1 : ψ (yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀) = 0 := by
        rw [← hz', map_smul, hka]
      rw [map_sub, sub_eq_zero] at h1
      exact h1
  exact h.comp_continuous continuous_subtype_val

end Loc

end Formalism.MainNotions.N.K.TBb

end
