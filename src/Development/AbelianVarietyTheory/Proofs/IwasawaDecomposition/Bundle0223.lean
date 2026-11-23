module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.Half

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


set_option maxHeartbeats 1600000 in
theorem preChar_updFW {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL Ks (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)
    (h : PreChar R) : PreChar (updFW R nW FW) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

section Upd

variable (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)


set_option maxHeartbeats 1600000 in
def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    OMDat T.toCore (updFW R nW FW) i Tp tup := { O with }

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

set_option maxHeartbeats 1600000 in
theorem omPins_upd (i : Fin D.R.m) (h : OMPins T R κ v₀ O i) :
    OMPins T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

set_option maxHeartbeats 1600000 in
theorem fired_upd (ph : Fin D.R.m → ℂ) (h : Fired T R κ v₀ O ph) :
    Fired T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) ph :=
  ⟨fun i => h.1 i, fun i σ hσ hV => h.2 i σ hσ hV⟩

end Upd

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))


set_option maxHeartbeats 1600000 in
def tieGeo (h : TieIn T R κ v₀) : FWTie T (geoR T R κ v₀ O) κ v₀ :=
  let t := tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ)
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

set_option maxHeartbeats 1600000 in
theorem barTie_tieGeo (h : TieIn T R κ v₀) : BarTie (tieGeo T R κ v₀ O h) :=
  fun i σ hσ hV => barTie_tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ) i σ hσ hV

set_option maxHeartbeats 1600000 in
theorem rhoGeo_tieGeo (h : TieIn T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) :
    RhoGeo (tieGeo T R κ v₀ O h) (fun i => updO T R _ _ (O i)) := by
  intro i
  have hb := hasB_nTop T h.laws κ i
  refine ⟨fun hk g f => ?_, fun hk g => ?_⟩
  · have hex := GlobalTheory.LevelRep.exists_cusp_rep T κ i (O i).lev2 h.laws (hp i).2.act.1 hk
    refine ⟨hk g f f.2, ?_⟩
    have e1 : geoRho T R κ O i = rhoB D.what₂.LL hb.some hex.choose := dif_pos ⟨hb, hex⟩
    have e2 : (⟨_, hk g f f.2⟩ : Cu T κ i) = hex.choose g f := Subtype.ext (hex.choose_spec g f).symm
    show crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) ⟨_, hk g f f.2⟩ =
      geoRho T R κ O i g (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) f)
    rw [e1, e2, crdOr_eq hb, rhoB_crd]
  · have e1 : geoRho T R κ O i = 1 := dif_neg fun h' => hk fun g f hf => by
      have h1 := h'.2.choose_spec g ⟨f, hf⟩
      have h2 := (h'.2.choose g ⟨f, hf⟩).2
      rw [h1] at h2
      exact h2
    show geoRho T R κ O i g = 1
    rw [e1]
    rfl

set_option maxHeartbeats 1600000 in
theorem chiIs_chiTop_of_tie (hL : R.toLevCh.Is A.μ0) (h : TieIn T R κ v₀) (i : Fin D.R.m) : ChiIs R i (chiTop R i) := by
  choose y ha using GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hL h i
  have hne : ∀ g, algebraMap T.Q.c.F D.what₂.LL (y g) ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 _ (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.RealGeo.Half

namespace GlobalTheory.RealGeo


set_option maxHeartbeats 1600000 in
theorem exists_geoHalf_geoR : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O ph hc ht hp hf
  have hf' := Half.fired_upd T R κ v₀ (nTop T κ) (formsGeo T R κ v₀ O) O ph hf
  refine ⟨⟨κ, v₀, Half.tieGeo T R κ v₀ O ht, Half.barTie_tieGeo T R κ v₀ O ht, fun i => Half.updO T R _ _ (O i),
    fun i => Half.omPins_upd T R κ v₀ _ _ O i (hp i), Half.rhoGeo_tieGeo T R κ v₀ O ht hp,
    fun i σ hσ hV _ => hf'.2 i σ hσ hV, fun i _ => ⟨ph i, hf'.1 i⟩, fun i _ _ => hf'.1 i⟩,
    rfl, rfl, hf', Half.preChar_updFW R _ _ hc, fun i g => ?_⟩
  exact (Half.chiIs_chiTop_of_tie T R κ v₀ hc.lev ht i g).trans (Units.coe_prod _ _)

end GlobalTheory.RealGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFundamentalDomainIsometryTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem haar_fd_phi : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  intro D V V' I S μ 𝓕 hμ h𝓕
  haveI hB : BorelSpace (WO S V) := ⟨rfl⟩
  haveI hB' : BorelSpace (WO S V') := ⟨rfl⟩
  have hc := I.continuous_phi S
  have hcs := I.continuous_phi_symm S
  have hrat : ∀ x, I.phi S x ∈ ratL V' S ↔ x ∈ ratL V S := by
    intro x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨I.Q * z, ?_⟩
      have h1 := I.symm.phi_ratW S z
      have h2 : ratW V' S z = I.phi S x := hz
      rw [h2, ← I.phi_symm_apply, AddEquiv.symm_apply_apply] at h1
      exact h1.symm
    · rintro ⟨z, hz⟩
      refine ⟨I.P * z, ?_⟩
      have h1 := I.phi_ratW S z
      have h2 : ratW V S z = x := hz
      rw [h2] at h1
      exact h1.symm
  let m : WO S V ≃ᵐ WO S V' :=
    { toEquiv := (I.phi S).toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hcs.measurable }
  have hmp : MeasurePreserving m (μ.map m.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving (I.phi S) (μ.map (I.phi S).symm) μ := hmp
  refine ⟨μ.map (I.phi S).symm, I.phi S ⁻¹' 𝓕, AddEquiv.isAddHaarMeasure_map μ (I.phi S).symm hcs (by simpa using hc), ?_, ?_⟩
  · let f : ratL V' S → ratL V S := fun y => ⟨(I.phi S).symm y, (hrat _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext ((I.phi S).symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨I.phi S x, (hrat _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro u
    have := hmp'.setLIntegral_comp_preimage_emb m.measurableEmbedding (fun b => u ((I.phi S).symm b)) 𝓕
    simpa using this.symm

end GlobalTheory.Mem.Isom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInnerProductSpace
section
noncomputable section

namespace GlobalTheory.Mem.SStageInhab

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

theorem ncard_primesOver_eq (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime) :
    ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).ncard = (placesOver E l).ncard := by
  symm
  apply Set.ncard_congr (fun v _ => v.asIdeal)
  · intro v hv
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl)) (by simpa using hl.ne_zero)
    refine hm.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ v.asIdeal)) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [Ideal.under, placesOver] using hv
  · intro a b _ _ h; exact HeightOneSpectrum.ext h
  · rintro P ⟨hP, hP'⟩
    have hmem : ((l:ℕ) : 𝓞 E) ∈ P := by
      have : (l:ℤ) ∈ P.under ℤ := by rw [← hP'.over]; exact Ideal.mem_span_singleton_self _
      simpa [Ideal.under] using this
    refine ⟨⟨P, hP, ?_⟩, hmem, rfl⟩
    rintro rfl
    exact hl.ne_zero (by simpa using hmem)

theorem conjF_ne_id (B : Base) : B.toPre.conjF ≠ AlgHom.id _ _ := by
  letI := B.host.cmStar
  intro h
  have h2 := B.sp.cm.deg2
  have hs : Function.Surjective (algebraMap B.host.F B.host.E) := fun a => by
    have : B.toPre.conjF a = a := by rw [h]; rfl
    exact (B.sp.cm.fixed a).1 this
  have : Module.finrank B.host.F B.host.E = 1 := by
    rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap.symm] ; exact ⟨(algebraMap B.host.F B.host.E).injective, hs⟩
  omega

theorem exists_locAt_split_iff (B : Base) (h2 : Module.finrank B.host.F B.host.E = 2) (hne : B.toPre.conjF ≠ AlgHom.id _ _) (p) :
    ∃ L : Formalism.MainNotions.S.Loc.LocAt B.host.F B.host.E B.toPre.conjF p, (L.split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  obtain ⟨L, hL⟩ := GlobalTheory.LocalData.exists_locAt _ _ B.toPre.conjF h2 p
  by_cases h : Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt _ _ _ h2 hne p L (by
      rw [ncard_primesOver_eq _ _ L.ellPrime.out]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> rw [h] <;> exact B.toPre.g_split _)
    exact ⟨{L with split := some S}, by simp [h]⟩
  · exact ⟨L, by simp [hL, h]⟩

theorem nonempty_conj_embedding (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] (d D : ℕ) (h : d ≤ D)
    (b : OrthonormalBasis (Fin d) ℂ EE) : Nonempty (EE →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin D)) := by
  let e := EuclideanSpace.basisFun (Fin D) ℂ
  have ho : Orthonormal ℂ (fun i : Fin d => e (Fin.castLE h i)) := e.orthonormal.comp _ (Fin.castLE_injective h)
  let f : EE →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ (Fin D) :=
    { toFun := fun x => ∑ i, (inner ℂ x (b i)) • e (Fin.castLE h i)
      map_add' := by intro x y; simp [inner_add_left, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul, mul_comm] }
  refine ⟨⟨f, fun x => ?_⟩⟩
  have h1 : inner ℂ (f x) (f x) = ∑ i, (starRingEnd ℂ) (inner ℂ x (b i)) * inner ℂ x (b i) :=
    ho.inner_sum _ _ _
  have h2 := b.sum_inner_mul_inner x x
  have h3 : inner ℂ (f x) (f x) = inner ℂ x x := by
    rw [h1, ← h2]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_conj_symm, mul_comm]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
  have h4 : ‖f x‖^2 = ‖x‖^2 := by exact_mod_cast h3
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4

theorem exists_innerProductSpace (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ip : V → V → ℂ)
    (hs : ∀ x y, (starRingEnd ℂ) (ip y x) = ip x y) (hp : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (ha : ∀ x y z, ip (x+y) z = ip x z + ip y z) (hm : ∀ x y (r:ℂ), ip (r • x) y = (starRingEnd ℂ) r * ip x y) :
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : FiniteDimensional ℂ U) (e : U ≃ₗ[ℂ] V),
      ∀ x y, inner ℂ x y = ip (e x) (e y) := by
  let c : InnerProductSpace.Core ℂ V :=
    { inner := ip, conj_inner_symm := hs
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · have := hm x x 0; subst h; simp at this; simp [this]
        · exact (hp x h).le
      add_left := ha, smul_left := hm
      definite := fun x h => by by_contra h'; have := hp x h'; rw [h] at this; simp at this }
  letI n : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI i : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  exact ⟨V, n, i, inferInstance, LinearEquiv.refl _ _, fun x y => rfl⟩

theorem exists_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) :
    ∃ S : SStage B C W, S.s.Del = Del ∧ S.s.letter = letter ∧ (∀ u u', Nonempty (S.s.Term u u')) ∧
      ∀ u u', Nonempty (S.s.Pair u u') := by
  have hloc := by
    letI := B.host.cmStar
    exact exists_locAt_split_iff B B.sp.cm.deg2 (conjF_ne_id B)
  choose L hL using hloc
  let pt : Formalism.MainNotions.S.Point B.host.E (B.R.rS + 1) := ⟨[(1, B.R.rS + 1)], by simp, by simp⟩
  have hU := fun u => by
    haveI := (C.mem u).A.Mu0_fd
    exact exists_innerProductSpace (C.mem u).A.Mu0 (fun x y => (C.fm u).ipC 0 x.1 y.1) (fun x y => hs u _ x.2 _ y.2)
      (fun x hx => hp u _ x.2 (fun h => hx (Subtype.ext h)))
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun x y r => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  choose U n i f e he using hU
  obtain ⟨sE⟩ := nonempty_conj_embedding W.EE _ _ hDD W.onb
  let s : Formalism.MainNotions.S.Draft.SData B.R B.host.F B.host.E B.toPre.conjF B.Word (Tau B.R) B.hcW :=
    { cdScale := fun _ _ => 1, cdScale_pos := fun _ _ => one_pos, Del := Del, Del_pos := hD, cloud_gap := gap
      letter := letter, letter_inj := hinj, u_letter := hu, HH := EuclideanSpace ℂ (Fin W.Dall)
      Cu := U, cuN := n, cuI := i, cuF := f, Pu := fun _ => 0, volN := fun _ => 1, volH := fun _ => 1
      volN_pos := fun _ => one_pos, volH_pos := fun _ => one_pos, Term := fun _ _ => Unit
      aTerm := fun _ _ _ => 0, isId := fun _ => True, inS := fun _ => True, relevant := fun _ => True
      FeqF := fun _ => True, Gterm := fun _ => 0, atP := L, PlF := HeightOneSpectrum (𝓞 B.host.F)
      BBne := fun _ _ => False, generic := fun _ => False, Pair := fun _ _ => Unit
      pfst := fun _ => (), psnd := fun _ => (), s0 := fun _ => 0, scalarPair := fun _ => True
      pval := fun _ => 0, ptOf := fun _ => pt, cTerm := fun _ => 1, massPair := fun _ => 1
      meanCount := fun _ _ _ => 0 }
  exact ⟨{ dsig := fun _ => 1, dsig_pos := fun _ => one_pos, s := s, s_split := hL, s_HH := by simp [s]
           s_Cu := e, s_PlF := Equiv.refl _, s_Cu_isom := he, sEE := sE },
    rfl, rfl, fun _ _ => ⟨()⟩, fun _ _ => ⟨()⟩⟩

theorem nonempty_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) : Nonempty (SStage B C W) :=
  (exists_sStage B C W Del hD gap letter hinj hu hs hp hDD).elim fun S _ => ⟨S⟩

end GlobalTheory.Mem.SStageInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfIsotypicCommutingSubgroups
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

theorem exists_multilinearMap_of_isotypic_commuting :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
      (H : ι → Type) [∀ v, Group (H v)] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)]
      [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (ρ : Representation ℂ G V)
      (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v)),
      Nontrivial V → (∀ v, (σ v).IsIrreducible) →
      (∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b)) →
      (∀ v, (⨆ f : (σ v).IntertwiningMap (ρ.comp (s v)), LinearMap.range f.toLinearMap) = ⊤) →
      ∃ F : (∀ v, Wv v) →ₘₗ[ℂ] V, F ≠ 0 ∧ ∀ v (h : H v) (x : ∀ u, Wv u),
        ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))) := by
  intro ι _ _ G V _ _ _ H _ Wv _ _ _ ρ s σ hV hirr hcomm hspan
  have hfac : ∀ v, ∃ Φ : Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V,
      (∀ h, Φ (σ v h) = ρ (s v h)) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ (s v h))) → ∀ A, Commute T (Φ A) :=
    fun v => _root_.GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners (H v) (Wv v) V (σ v) (ρ.comp (s v)) (hirr v) (hspan v)
  choose Φ hΦσ hΦc using hfac
  have hΦcomm : ∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B) := by
    intro u v huv A B
    have h1 : ∀ b, Commute (ρ (s v b)) (Φ u A) := by
      intro b
      refine hΦc u _ (fun a => ?_) A
      exact ((hcomm v u (Ne.symm huv) b a).map ρ)
    exact hΦc v (Φ u A) (fun b => (h1 b).symm) B
  have hnt : ∀ v, Nontrivial (Wv v) := fun v => ((GlobalTheory.CuspRep.isIrreducible_iff _).1 (hirr v)).1
  have hw : ∀ v, ∃ w : Wv v, w ≠ 0 := fun v => exists_ne 0
  choose w hw0 using hw
  have hl : ∀ v, ∃ ℓ : Module.Dual ℂ (Wv v), ℓ (w v) = 1 := by
    intro v
    have hn : w v ∉ (⊥ : Submodule ℂ (Wv v)) := by simpa using hw0 v
    obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    exact ⟨(f (w v))⁻¹ • f, by simp [hf]⟩
  choose ℓ hℓ using hl
  obtain ⟨y, hy0, hy⟩ := _root_.GlobalTheory.commuting_endAlgebras_common_fixed_vector ι Wv V Φ w ℓ hV hℓ hΦcomm
  obtain ⟨F, hFw, hF⟩ := _root_.GlobalTheory.exists_multilinear_of_commuting_endAlgHom ι Wv V Φ w ℓ y hΦcomm hy
  refine ⟨F, fun h0 => hy0 ?_, fun v h x => ?_⟩
  · rw [← hFw, h0]; rfl
  · rw [← hΦσ v h]
    exact hF v (σ v h) x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBaseFramesFlagDomainModels
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.BaseFrame

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem gram_x0Mat {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ} (hr : V.rank = r) (ρ : D.what₂.Tau)
    {p q : ℕ} (hpq : r = p + q) (hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
      (Matrix.reindex (finCongr hr) (finCongr hr) (x0Mat M ρ)) =
      Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  subst hr
  have hp : p ≤ V.rank := by omega
  have hq : nNeg (M.ε ρ) = q := (nNeg_shape hp hε).trans (by omega)
  have h0 : ∀ x : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) x = (-(xᴴ * gramAt D V ρ * x))ᵀ := fun x => by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, transpose_apply, Matrix.neg_apply, Matrix.mul_apply,
      conjTranspose_apply, gramAt, map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring
  have hinv : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have h1 : ((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹ = Formalism.REAL.Jm (M.ε ρ) := by
    rw [← M.fr_gram ρ]
    calc _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv]; simp
  have h2 : (x0Mat M ρ)ᴴ * gramAt D V ρ * x0Mat M ρ =
      (((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹).submatrix (arr (nNeg (M.ε ρ))) (arr (nNeg (M.ε ρ))) := rfl
  show ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) (x0Mat M ρ) = _
  rw [h0, h2, h1, hq]
  ext a c
  have ha := a.2
  have hc := c.2
  simp only [transpose_apply, Matrix.neg_apply, submatrix_apply, Formalism.REAL.Jm, diagonal_apply, hε, sgn, arr, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem exists_baseFrame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  intro D G _ _ Pl0 T0 A T _ R hL hA hF
  classical
  let x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ := fun j s τ =>
    if h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau, j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2 then
      Matrix.reindex (finCongr (rank_Wc h.choose.1)) (finCongr (rank_Wc h.choose.1))
        (x0Mat (R.MW h.choose.1 h.choose.2.1) h.choose.2.2)
    else T.x₀ j s τ
  have key : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ)) := by
    intro i σ ρ
    have h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        (i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2 := ⟨(i, σ, ρ), rfl, rfl, rfl⟩
    have aux : ∀ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        ((i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2) →
        Matrix.reindex (finCongr (rank_Wc p.1)) (finCongr (rank_Wc p.1)) (x0Mat (R.MW p.1 p.2.1) p.2.2) =
          Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (x0Mat (R.MW i σ) ρ) := by
      rintro ⟨i', σ', ρ'⟩ ⟨h1, h2, h3⟩
      obtain rfl : i = i' := Fin.ext (Nat.add_right_cancel h1)
      obtain rfl : ρ = ρ' := tauE_injective h3
      rw [hF.1 i σ σ' h2 ρ]
    exact (dif_pos h).trans (aux _ h.choose_spec)
  refine ⟨x₀, fun i σ _ => key i σ, fun j hj s hs k τ hτ => ?_⟩
  by_cases h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
      j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2
  · obtain ⟨⟨i, σ, ρ⟩, rfl, rfl, rfl⟩ := h
    dsimp only at hj hs k hτ ⊢
    have hU := hL.unf _ hj _ hs
    have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hL.pins.2.2.2 _ hj).1
    have hM : ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) (res T σ)).X k) := by
      obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hs
      have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hL.spaceW _ hj _ hs
      have h1 := hm k
      revert hr
      rw [hV]
      exact fun _ _ h => h
    have hε : ∀ a, (R.MW i σ).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun a => by
      rw [hF.2 i σ (fun ρ' => (GlobalTheory.HolRead.good_iff_labE_and_lab_conj D T hL hA σ ρ').1.1 hs) ρ a, hdp,
        show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    rw [key i σ ρ, hM.1, (hU.2.1 k).1]
    exact gram_x0Mat _ _ ρ hU.1 hε
  · have e : x₀ j s τ = T.x₀ j s τ := dif_neg h
    rw [e]
    exact hL.familyUniformisationBasePointOrthogonal j hj s hs k τ hτ

end GlobalTheory.RealGeo.BaseFrame
end

