module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCuspFormTransvectionConstantTermsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.PtDeco

theorem isPtOf_iff_decoRaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), Q = ∅ → (IsPtOf hc g p ↔ g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g p hQ
  subst hQ
  have hlast : ∀ i : Fin n, i.1 + 1 = n → lastIdx n = i := fun i hi => Fin.ext (by simp [lastIdx]; omega)
  constructor
  · intro h
    have hg : g ∈ UAd hc n := h.uni
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by
      have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
        let L := p.deco.1.N
        let W := Submodule.span E (L : Set (Sp E n))
        change W = ⊤
        by_contra hW
        let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
        let f : Sp E n →ₗ[E] Module.Dual E W :=
          (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
        have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt hW
        obtain ⟨x, hx, hx₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
        have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
        have hsmul (a : E) : a • e x ∈ L := by
          rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
          intro y hy
          apply hStd_mem_one_symm
          have hxy : hStd E n (e x) y = 0 :=
            congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
          simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
        let i : E →ₗ[𝓞 E] L :=
          ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
        let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
        let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
          smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
      have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg)
        hspan
      ext v
      conv_lhs => rw [← h1]
      have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
          v ∈ Formalism.UG.CS.globLat x Λ ↔ ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        fun _ _ _ => Iff.rfl
      rw [e1, e1, inv_one, Units.val_one, Matrix.one_mulVec]
      exact h.lat _
    refine ⟨hg, Deco.Ok.ext_on p.deco.2 (decorated_lattice_exists hc n ST SG g hg) hN (fun P x hx => ?_) (fun w x hx => ?_)⟩
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      refine HasRes.unique (h.f P x hx (lastIdx n) (by simp [lastIdx]; have := NeZero.pos n; omega)) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' _)
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      funext i
      refine HasRes.unique (h.be w x hx i) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' i)
  · rintro ⟨hg, hd⟩
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by rw [hd]; rfl
    refine ⟨hg, hN ▸ PtExist.carries_globLat g, fun P x hx i hi => ?_, fun w x hx i => ?_,
      fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx), hlast i hi]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx)]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)

end GlobalTheory.Mem.Col2.PtDeco

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicHeckeOperatorHyperspecialActsByScalar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.IsoTypScalar

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem heckeD_eq_sum_of {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {J : Subgroup (GAf L n)}
    (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  have tr : ∀ x ∈ D, ∀ y ∈ D, TrivOutside {v} (x⁻¹ * y) := fun x hx y hy =>
    GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy)
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dite_eq_left hc]
    have ht := tr γ (h1 γ hγ) _ hc.choose_spec.1
    have hu : γ⁻¹ * hc.choose ∈ Umax L n := (hJ _ ht).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)
    have := congrFun (hf _ hu ht) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, (hJ _ (tr γ (h1 γ hγ) δ (h1 δ hδ))).1 (QuotientGroup.eq.1 e)⟩
      ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hJ _ (tr γ (h1 γ hγ) x hx)).2 e)⟩)
    · exact absurd (dite_eq_right h) hc

theorem isoTyp_scalar (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L))))
    (hyp : NG.HypOutside J χ B) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ) (hsB : s.v ∉ B) (hϖ : IsUnif L s.v ϖ) :
    ∃ c : ℂ, ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → NG.tN J s ϖ k f = c • f := by
  classical
  have tc : ∀ κ : GAf L n, TrivOutside {s.v} κ → TrivOutside Bᶜ κ := fun κ hκ v hv =>
    hκ v fun h => hv (by rw [Set.mem_compl_iff, Set.mem_singleton_iff.1 h]; exact hsB)
  have hJU : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n) := fun κ hκ => (hyp κ (tc κ hκ)).1
  have hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite :=
    _root_.GlobalTheory.TSetFin.finite_image_tSet L n (Umax L n) 1 ∅ (fun κ _ => ⟨Iff.rfl, fun _ => MonoidHom.one_apply _⟩) s ϖ k
      (Set.notMem_empty _) hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_reps (Umax L n) _ hfin
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun _ hx => hx.1
  set q : ℂ := ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ with hq
  have hJeq : ∀ f : GAf L n → a.W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      NG.tN J s ϖ k f = q • ∑ γ ∈ R, NG.rt L n γ f := fun f hf => by
    rw [NG.tN, heckeD_eq_sum_of hJU hD hR1 hR2 hf]
  have hUeq : ∀ f : GAf L n → a.W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      NG.tN (Umax L n) s ϖ k f = q • ∑ γ ∈ R, NG.rt L n γ f := fun f hf => by
    rw [NG.tN, GlobalTheory.HeckeScalarSph.heckeD_eq_sum (v := s.v) hD hR1 hR2 hf]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.HeckeScalarSph.tN_scalar L n a S hS s ϖ k hϖ
  have hS0 : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      q • ∑ γ ∈ R, NG.rt L n γ f = c • f := fun f hf hx => (hUeq f hx).symm.trans (hc f hf hx)

  have hiso : ∀ S' : Submodule ℂ (GAf L n → a.W), NG.IsoRep S S' → ∀ f ∈ S',
      (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → q • ∑ γ ∈ R, NG.rt L n γ f = c • f := by
    rintro S' ⟨T, hT⟩ f hf hfx
    set g : S := T.symm ⟨f, hf⟩ with hg
    have hTg : ((T g : S') : GAf L n → a.W) = f := by simp [g]
    have hgx : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (g : GAf L n → a.W) = g := by
      intro κ h1 h2
      have e := hT κ g ⟨NG.rt L n κ (g : GAf L n → a.W), hS.1.stable κ _ g.2⟩ rfl
      rw [hTg, hfx κ h1 h2] at e
      have e2 : T ⟨NG.rt L n κ (g : GAf L n → a.W), hS.1.stable κ _ g.2⟩ = T g := Subtype.ext (e.trans hTg.symm)
      exact congrArg Subtype.val (T.injective e2)
    have key : (c • g : S) = q • ∑ γ ∈ R, (⟨NG.rt L n γ (g : GAf L n → a.W), hS.1.stable γ _ g.2⟩ : S) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_sum]
      exact (hS0 g g.2 hgx).symm
    have hterm : ∀ γ : GAf L n,
        ((T ⟨NG.rt L n γ (g : GAf L n → a.W), hS.1.stable γ _ g.2⟩ : S') : GAf L n → a.W) = NG.rt L n γ f := by
      intro γ
      rw [hT γ g _ rfl, hTg]
    have := congrArg (fun u : S => ((T u : S') : GAf L n → a.W)) key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Submodule.coe_smul, Submodule.coe_sum, hTg, hterm] at this
    exact this.symm

  have hsum : ∀ t : Finset (Submodule ℂ (GAf L n → a.W)),
      (↑t : Set (Submodule ℂ (GAf L n → a.W))) ⊆ {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'} →
      (∀ h, ∀ f ∈ ⨆ S' ∈ t, S', NG.rt L n h f ∈ ⨆ S' ∈ t, S') ∧
      ∀ f ∈ ⨆ S' ∈ t, S', (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
        q • ∑ γ ∈ R, NG.rt L n γ f = c • f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot]
      refine ⟨fun h f hf => ?_, fun f hf _ => ?_⟩
      · rw [hf, map_zero]
      · simp [hf]
    | insert S₁ t hS₁ ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨hst, hfx⟩ := ih hs.2
      have h1 := hs.1
      rw [Finset.iSup_insert]
      refine ⟨fun h f hf => ?_, fun f hf hfix => ?_⟩
      · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hf
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (h1.1.1.stable h x hx) (hst h y hy)
      · by_cases hd : S₁ ⊓ (⨆ S' ∈ t, S') = ⊥
        · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hf
          have hxy : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ x = x ∧ NG.rt L n κ y = y := by
            intro κ hκ hκ'
            have e := hfix κ hκ hκ'
            rw [map_add (f := _)] at e
            have e1 : NG.rt L n κ x - x = y - NG.rt L n κ y := by
              rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
            have hm : NG.rt L n κ x - x ∈ S₁ ⊓ (⨆ S' ∈ t, S') :=
              ⟨S₁.sub_mem (h1.1.1.stable κ x hx) hx, e1 ▸ Submodule.sub_mem _ hy (hst κ y hy)⟩
            rw [hd, Submodule.mem_bot] at hm
            refine ⟨sub_eq_zero.1 hm, ?_⟩
            rw [hm] at e1
            exact (sub_eq_zero.1 e1.symm).symm
          simp only [map_add (f := _), Finset.sum_add_distrib, smul_add]
          rw [hiso S₁ h1.2 x hx fun κ h h' => (hxy κ h h').1, hfx y hy fun κ h h' => (hxy κ h h').2]
        · have hsub : NG.IsSubrep a.ρ (S₁ ⊓ (⨆ S' ∈ t, S')) :=
            ⟨inf_le_left.trans h1.1.1.le, fun h f hf => ⟨h1.1.1.stable h f hf.1, hst h f hf.2⟩⟩
          have heq : S₁ ⊓ (⨆ S' ∈ t, S') = S₁ := (h1.1.2.2 _ hsub inf_le_left).resolve_left hd
          have hle : S₁ ≤ ⨆ S' ∈ t, S' := heq ▸ inf_le_right
          exact hfx f ((sup_le hle le_rfl) hf) hfix
  refine ⟨c, fun f hf hT => ?_⟩
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f := by
    intro κ h1 h2
    have hκ : κ ∈ J := (hJU κ h2).2 h1
    have e := hT.2 ⟨κ, hκ⟩
    rw [(hyp κ (tc κ h2)).2 hκ] at e
    simpa using e
  rw [hJeq f hfix]
  unfold NG.isoTyp at hf
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact (hsum t ht).2 f hft hfix

theorem main : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := by
  intro D μ j Mr B _ hyp S hS s ϖ k hsB hϖ _ _
  obtain ⟨c, hc⟩ := isoTyp_scalar Mr.wt Mr.J Mr.χ B hyp S hS s ϖ k hsB hϖ
  refine ⟨c, fun y hy => hc _ (Submodule.mem_comap.1 hy) ?_⟩
  rw [← Mr.real_range]
  exact ⟨y, rfl⟩

end GlobalTheory.IsoTypScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspValues

theorem evEx_of_range {K C H X : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (σ : K →+* ℂ) (ev : H →ₗ[ℂ] X) (hinj : Function.Injective ev) (φ : C →ₛₗ[σ] X)
    (h : ∀ f, φ f ∈ LinearMap.range ev) : EvEx σ ev φ := by
  choose x hx using h
  refine ⟨⟨⟨x, fun f f' => hinj ?_⟩, fun a f => hinj ?_⟩, hx⟩
  · rw [map_add (f := _), hx, hx, hx, map_add (f := _)]
  · exact (hx _).trans (by rw [φ.map_smulₛₗ, map_smul, hx])

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
        (rdU (T.U j σ) f) := by
  subst hV
  rfl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

noncomputable def evLin {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' a b := by simp [evAt]
  map_smul' c a := by simp [evAt]


set_option maxHeartbeats 1000000 in
theorem jEvExists (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (ht : TieIn T R κ v₀) (hp : T.pb = R.C.P.pb) : JEvExists T R κ v₀ := by
  intro i σ hσ hV
  obtain ⟨hsh, -, w, hw⟩ := _root_.GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ ht i σ hσ
  have hg := _root_.GlobalTheory.HolDict.goodDict_core D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV w hw
  obtain ⟨-, hχ, hfin, -⟩ := _root_.GlobalTheory.HolDict.PrincLev.principal_level D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV
  have hinj : Function.Injective (evLin R i σ (v₀ i σ)) :=
    GlobalTheory.EvalAtUnitVector.evInj T R v₀ hM.HW ht.hv₀ i σ hσ
  let ad := adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ)))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ)))
      (T.cE ((i : ℕ) + 1) (res T σ)))
  have key : holSub (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) ≤
      (LinearMap.range (evLin R i σ (v₀ i σ))).comap ad := by
    refine Submodule.span_le.2 fun P hP => ?_
    have h1 := _root_.GlobalTheory.HolDict.BackHol.holForm_adel D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hsh hg P fun k => (hP k).1
    have h2 := _root_.GlobalTheory.HolDict.TransvCusp.zCusp_adel D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hsh hg P hP
    have h3 : GlobalTheory.HolDict.HolForm R.θ (R.MW i σ) w (levS _ (R.βW i) (R.datWp i R.triv))
        (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (ad P) :=
      ⟨h1.aut, h1.bdd, fun k hk g => by rw [hχ k hk]; exact h1.lev k hk g, h1.hol⟩
    obtain ⟨Tm, hT, hTv⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D R.θ _ _ (R.MW i σ) w (v₀ i σ) hM.inf hsh hw (ht.hv₀ i σ).1
      (GlobalTheory.HolDict.exists_finPair GlobalTheory.Mem.VolFin.finVol D _) _ _ _ hfin h3 h2
    have hmem : Tm ∈ R.Wall i σ := Submodule.subset_span hT
    rw [← (hM.HW i σ).2.1] at hmem
    obtain ⟨x, rfl⟩ := hmem
    exact ⟨x, hTv⟩
  let φ : Cu T κ i →ₛₗ[res T σ] (GA D (Wc D i) → ℂ) :=
    ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) • ad).comp
      ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype)
  have h := evEx_of_range (res T σ) _ hinj φ fun f =>
    Submodule.smul_mem _ _ (key (((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hσ))
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun f => (hj f).trans (phiC_eq T hV _ _).symm⟩

theorem jEvExists_and_jEvBar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hp
  have h := jEvExists T R κ v₀ hL hM ht hp
  exact ⟨h, (_root_.GlobalTheory.ConjHilb.conj_hilbert D G Pl0 T0 A T R κ v₀ hM ht).2 h⟩

end GlobalTheory.CuspValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamRdefEqSgTrue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowWeight

lemma isWtOfPar_eq {N n : ℕ} (h : N = n) {lam : DomWeight N} {S : SPar} (hS : Bridge.IsWtOfPar lam S)
    (hs : ∀ x ∈ S, x.2 = true) (c' : Fin n → ℚ) (hc' : StrictAnti c') (hm' : ∀ i, (c' i, true) ∈ S) (i : Fin N) :
    (lam.w i : ℚ) = c' (Fin.cast h i) - rhoVec n (Fin.cast h i) := by
  subst h
  obtain ⟨hcard, c, hc, hm, hw⟩ := hS
  have key : ∀ d : Fin N → ℚ, StrictAnti d → (∀ i, (d i, true) ∈ S) → Set.range d = {x | (x, true) ∈ S} := by
    intro d hd hdm
    have h1 : Finset.univ.image (fun i => (d i, true)) = S := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdm i
      · rw [Finset.card_image_of_injective _ (fun x y h => hd.injective (Prod.ext_iff.mp h).1), hcard]
        simp
    ext x
    rw [← h1]
    simp
  have hm2 : ∀ i, (c i, true) ∈ S := fun i => by
    obtain ⟨s, hs'⟩ := hm i
    have : s = true := hs _ hs'
    rwa [this] at hs'
  have e : c = c' := (hc.range_inj hc').1 ((key c hc hm2).trans (key c' hc' hm').symm)
  rw [hw, e]
  rfl

lemma sgHC_mem {R : Ranks} (P : HCParam R) (n : ℕ) (hn : n < R.N R.m - 1) :
    ∃ x, GlobalTheory.ForcedWeights.entry P x = (Formalism.L2.Col.RowPar.of P).sgHC n - Formalism.L2.Col.RowPar.sh R := by
  have hk := R.m_add_three_le_k
  unfold Ranks.N at hn
  by_cases h1 : n < R.k - 1
  · refine ⟨.inl ⟨n, h1⟩, ?_⟩
    rw [Formalism.L2.Col.RowPar.sgHC_lo _ h1, Formalism.L2.Col.RowPar.vb_lo _ h1]
    simp [GlobalTheory.ForcedWeights.entry]
  · obtain ⟨B, ρ, hρ, rfl⟩ : ∃ B ρ, ρ < R.t + 1 ∧ n = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(n - (R.k - 1)) / (R.t + 1), (n - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (n - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    rcases ρ with _ | ρ
    · refine ⟨.inr (.inl ⟨B, hBm⟩), ?_⟩
      rw [Nat.add_zero, Formalism.L2.Col.RowPar.sgHC_b, Formalism.L2.Col.RowPar.bAt_of _ hBm]
      simp [GlobalTheory.ForcedWeights.entry]
    · refine ⟨.inr (.inr (⟨B, hBm⟩, ⟨ρ, by omega⟩)), ?_⟩
      rw [Formalism.L2.Col.RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega), Formalism.L2.Col.RowPar.eAt_of _ hBm]
      simp only [GlobalTheory.ForcedWeights.entry]
      push_cast
      ring

lemma sgHC_strictAnti {R : Ranks} (P : HCParam R) :
    StrictAnti fun i : Fin (R.N R.m - 1) => (Formalism.L2.Col.RowPar.of P).sgHC i.1 - Formalism.L2.Col.RowPar.sh R := by
  intro i j hij
  have h := Formalism.L2.Col.anti_sub_rho (N := R.N R.m - 1) (Formalism.L2.Col.RowPar.of P).sgHC
    (fun _ hn => Formalism.L2.Col.RowPar.sgHC_step P hn) hij.le
  have h2 : (i.1 : ℚ) < (j.1 : ℚ) := by exact_mod_cast (show i.1 < j.1 from hij)
  simp only [rhoVec] at h ⊢
  linarith

theorem lamRdef_eq (D : D7) (h : D.sp.X'.rank = D.R.N D.R.m - 1) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank) :
    (Bridge.lamRdef (Ptw D) τ).w i = (Formalism.L2.Col.RowPar.of (D.hc τ)).sgTrue.w (Fin.cast h i) := by
  have hF := GlobalTheory.ForcedWeights.lamRForced D τ
  rw [GlobalTheory.ForcedWeights.dpar_eq] at hF
  have h1 := isWtOfPar_eq h hF (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      rfl) _ (sgHC_strictAnti (D.hc τ)) (fun a => by
      obtain ⟨x, hx⟩ := sgHC_mem (D.hc τ) a.1 a.2
      exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, by rw [hx]⟩) i
  rw [← Formalism.L2.Col.RowPar.sgTrue_eq] at h1
  exact_mod_cast h1

theorem lamRdef_eq_sgTrue : ∀ (X : Stages) (τ : X.B.fields.Tau) (i : Fin X.toD7.sp.X'.rank), (Bridge.lamRdef (Ptw X.toD7) τ).w i = (X.B.wts.sgTrue τ).w (Fin.cast (RowAd.rank_X' X) i) :=
  fun X τ i => lamRdef_eq X.toD7 (RowAd.rank_X' X) τ i

end GlobalTheory.Mem.R3.RowWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftResidueTwistCharacterEqResChar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.LevResXi

theorem xiR_eq_map_resChar : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ (t : TupU I U) (PP : HeightOneSpectrum (𝓞 X.B.fields.E)), PP ∈ Formalism.L2.Col.QE I.sel t.1 →
      ∀ c : (𝓞 X.B.fields.E ⧸ PP.asIdeal)ˣ, L.xiR t PP c = Units.map X.toD7.what₂.embLL.toMonoidHom
        (Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) PP c) := by
  intro X px I U L hI hV hL t PP hPP c
  have hQ : PP ∈ L.Q t := by
    rw [hL.Q t]
    change PP ∈ Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t))
    rw [tup_ixOf]
    exact hPP
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.B.fields.E ⧸ PP.asIdeal)
  have hn : b ∉ PP.asIdeal := fun hm => c.ne_zero (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 hm)
  have h0 : (b : X.B.fields.E) ≠ 0 := fun e => hn ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  have h1 := hL.is.xiR t PP hQ b (Units.mk0 _ h0) c rfl hb.symm
  have ht : ∀ P, (I.xi (ixOf I U t)).TameAt P := fun P => hL.xiH t ▸ hL.is.xi_tame t P
  have h2 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads (ixOf I U t)) ht PP c b (Units.mk0 _ h0) rfl hb
  rw [tup_ixOf] at h2
  rw [hL.xiH t] at h1
  refine Units.ext ?_
  rw [h1]
  exact h2.symm

end GlobalTheory.Mem.LevResXi
end

