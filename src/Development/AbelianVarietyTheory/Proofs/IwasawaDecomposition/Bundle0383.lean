module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftMarked
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0008
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.HeckeEigConj

theorem proj_conjSplit {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L) :
    (GlobalTheory.HeckeFrob.conjSplit s).proj z = s.proj (conjAL L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    simp only [SplitPlace.proj, conjAL, GlobalTheory.HeckeFrob.conjSplit, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]; rfl

theorem map_loc_conjSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) {K' : Type}
    [Field K'] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* K') (x : GAf L n) :
    Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x) =
      GlobalTheory.LFun.ConjPlace.invT i n (s.loc n x) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]
  have h := congrFun₂ (GlobalTheory.FinTypCount.inv_val x) b a
  change i ((GlobalTheory.HeckeFrob.conjSplit s).proj _) = i (s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix _ _ _) b a))
  rw [h, proj_conjSplit]
  rfl

theorem KO_eq_KGL (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := by
  ext g
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff]
  have h : ∀ x : w.adicCompletion E, x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (Valuation.mem_integer_iff _ _).trans (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w x)
  simp only [h]

theorem heckeD_eq_sum_of_agree {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  have hmem : ∀ x ∈ D, ∀ y ∈ D, (x⁻¹ * y ∈ J ↔ x⁻¹ * y ∈ Umax L n) := fun x hx y hy =>
    hJ _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy))
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dite_eq_left hc]
    have hu : γ⁻¹ * hc.choose ∈ Umax L n :=
      (hmem γ (h1 γ hγ) _ hc.choose_spec.1).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)
    have := congrFun (hf _ hu (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD γ (h1 γ hγ)))
      (hD _ hc.choose_spec.1))) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, (hmem γ (h1 γ hγ) δ (h1 δ hδ)).1 (QuotientGroup.eq.1 e)⟩
      ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hmem γ (h1 γ hγ) x hx).2 e)⟩)
    · exact absurd (dif_neg h) hc

theorem norms_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    Formalism.UG.qV L (GlobalTheory.HeckeFrob.conjSplit s).w = normV (GlobalTheory.HeckeFrob.conjSplit s).w ∧
      s.q = normV (GlobalTheory.HeckeFrob.conjSplit s).w := by
  refine ⟨?_, ?_⟩
  · rw [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV]
  · rw [normV, (GlobalTheory.HeckeFrob.conjSplit s).card_quot]
    rfl

end GlobalTheory.HeckeEigConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigensystemMultiplicities
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutPts

theorem l0 : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := GlobalTheory.T.splitPlace_outside_nonHyperspecial_of_localisation
theorem l1 : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := _root_.GlobalTheory.IsoTypScalar.main
theorem l2a : ∀ (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ) (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i), X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w)) (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := _root_.GlobalTheory.HeightCounting.mult_eq_finrank_jointEig
theorem l2b : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := _root_.GlobalTheory.PtLocalEig.eig_dim

theorem mt_tr {D : D7} (M : MtFam D) (Pr : ∀ (μ : D.what₂.Tup) (j : ℕ), MtReal D μ j → Prop) {μ μ' : D.what₂.Tup}
    {j j' : ℕ} (hμ : μ = μ') (hj : j = j') (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) :
    Pr μ j (M μ j a1 a2) → Pr μ' j' (M μ' j' b1 b2) := by
  subst hμ hj; exact id

theorem genAt_iff' {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    {X : LocNd (lay0 D)} {T : LocTw X} (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.what₂.places.resChar (X.nd.w i)) (Sp.B.Qc (X.nd.j i) (X.nd.w i)) v k ↔
      (SplitOut X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have h : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hl : X.nd.l i = D.what₂.places.resChar (X.nd.w i) := (X.nd.w_l i).symm
  have hS : v ∈ X.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar (X.nd.w i)) := by
    rw [X.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, Sp.Q_eq _ _ i h, hl]
  tauto

theorem mem_iSup_iff {V Wf : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Wf] [Module ℂ Wf] {ι : Type}
    [Finite ι] (real : V →ₗ[ℂ] Wf) (hreal : Function.Injective real) (typ : ι → Submodule ℂ V)
    (hind : iSupIndep typ) (htop : ⨆ P, typ P = ⊤) {Par : Type} (Good : Par → Prop) (op : Par → Wf → Wf)
    (hlin : ∀ p, Good p → ∀ (c : ℂ) (f f' : Wf), op p (c • f + f') = c • op p f + op p f')
    (hsc : ∀ P p, Good p → ∃ c : ℂ, ∀ y ∈ typ P, op p (real y) = c • real y) (lam : Par → ℂ) (Q : ι → Prop)
    (hQ : ∀ P, Q P ↔ ∀ p, Good p → ∀ y ∈ typ P, op p (real y) = lam p • real y) (y : V) :
    y ∈ (⨆ P ∈ {P | Q P}, typ P) ↔ ∀ p, Good p → op p (real y) = lam p • real y := by
  classical
  have hop0 : ∀ p, Good p → op p 0 = 0 := fun p hp => by
    have h := hlin p hp 1 0 0
    rw [one_smul, add_zero, one_smul] at h
    exact (add_eq_left.1 h.symm)
  have hopadd : ∀ p, Good p → ∀ f f' : Wf, op p (f + f') = op p f + op p f' := fun p hp f f' => by
    simpa using hlin p hp 1 f f'
  have hopsmul : ∀ p, Good p → ∀ (c : ℂ) (f : Wf), op p (c • f) = c • op p f := fun p hp c f => by
    simpa [hop0 p hp] using hlin p hp c f 0
  let Es : Submodule ℂ V :=
    { carrier := {y | ∀ p, Good p → op p (real y) = lam p • real y}
      zero_mem' := fun p hp => by simp [hop0 p hp]
      add_mem' := fun {a b} ha hb p hp => by
        simp only [map_add (f := _), hopadd p hp, ha p hp, hb p hp, smul_add]
      smul_mem' := fun c a ha p hp => by
        simp only [map_smul, hopsmul p hp, ha p hp, smul_comm c (lam p)] }
  show y ∈ _ ↔ y ∈ Es
  constructor
  · intro hy
    refine (iSup₂_le fun P hP => ?_ : (⨆ P ∈ {P | Q P}, typ P) ≤ Es) hy
    intro z hz p hp
    exact (hQ P).1 hP p hp z hz
  · intro hy
    have hy' : y ∈ ⨆ P, typ P := by rw [htop]; trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp typ y).1 hy'
    rw [← hsum]
    refine Submodule.finsuppSum_mem _ _ _ _ fun P hPs => ?_
    by_cases h0 : f P = 0
    · rw [h0]; exact Submodule.zero_mem _
    refine (le_iSup₂ (f := fun P (_ : P ∈ {P | Q P}) => typ P) P ?_) (hf P)
    show Q P
    refine (hQ P).2 fun p hp => ?_
    obtain ⟨c, hc⟩ := hsc P p hp
    choose cc hcc using fun P' => hsc P' p hp

    have hz : ∑ P' ∈ f.support, (cc P' - lam p) • f P' = 0 := by
      apply hreal
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, map_sum]
      have e1 : ∀ P' ∈ f.support, real ((cc P' - lam p) • f P') = op p (real (f P')) - lam p • real (f P') := by
        intro P' _
        rw [map_smul, hcc P' _ (hf P'), sub_smul]
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.smul_sum]
      have e2 : ∀ s : Finset ι, op p (real (∑ P' ∈ s, f P')) = ∑ P' ∈ s, op p (real (f P')) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [hop0 p hp]
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add (f := _), hopadd p hp, ih]
      have e3 : (∑ P' ∈ f.support, f P') = y := hsum
      have e4 : ∑ P' ∈ f.support, op p (real (f P')) = op p (real y) := by rw [← e2, e3]
      have e5 : ∑ P' ∈ f.support, real (f P') = real y := by rw [← e3, map_sum]
      rw [e4, e5, hy p hp, sub_self]
    have hz' := ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero typ).1 hind) f.support
      (fun P' => (cc P' - lam p) • f P') (fun P' _ => Submodule.smul_mem _ _ (hf P')) hz P
      (Finsupp.mem_support_iff.2 h0)
    have hcl : cc P = lam p := by
      rcases smul_eq_zero.1 hz' with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h h0
    intro z hz
    rw [hcc P z hz, hcl]

end GlobalTheory.AutPts

namespace GlobalTheory.AutPts


end GlobalTheory.AutPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

theorem mem_HHa_of_span {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : P ∈ Submodule.span k (HHa r n k cc isX a)) : P ∈ HHa r n k cc isX a := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, fun σ i i' hi t => by rw [map_add (f := _), hx.2.1 σ i i' hi t, hy.2.1 σ i i' hi t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx.2.2 m h
    · exact hy.2.2 m h
  | smul c x _ hx =>
    exact ⟨Submodule.smul_mem _ c hx.1, fun σ i i' hi t => by rw [map_smul, hx.2.1 σ i i' hi t],
      fun m hm => hx.2.2 m (MvPolynomial.support_smul hm)⟩

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : RowDeg r n k a P) : P.IsHomogeneous (∑ σ, ∑ j : Fin (r σ), a σ j) := by
  intro m hm
  have h1 := h m (MvPolynomial.mem_support_iff.2 hm)
  rw [show Finsupp.weight 1 m = Finsupp.degree m from (DFunLike.congr_fun Finsupp.degree_eq_weight_one m).symm,
    Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => h1 σ j

theorem exists_isVarOf {D : D7} (V W : HSp D) {r : ℕ} (hr : W.rank = r) (X : Data D.host.E r) (hX : IsMod W hr X) (q0 : ℕ)
    (hq : X.p0 + q0 = r) : ∃ vr, IsVarOf V W X q0 vr := by
  let e1 : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hX.psi _).2 ⟨ρ, rfl⟩⟩)
    ⟨fun a b h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hX.psi τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  let e2 : Fin q0 ⊕ Fin X.p0 ≃ Fin W.rank := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨e1.symm.prodCongr (e2.prodCongr (Equiv.refl _)), fun l => ⟨?_, rfl, ?_⟩⟩
  · exact (congrArg Subtype.val (e1.apply_symm_apply l.1)).symm
  · obtain ⟨τ, j | j, b⟩ := l <;> rfl

theorem exists_isDetAt {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    ∃ y, IsDetAt e V g y := by
  obtain ⟨ι, Q, es, h1, h2, h3⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum h
  have he : e * e = e := by
    conv_lhs => rw [h3, Finset.sum_mul]
    rw [h3]
    exact Finset.sum_congr rfl fun i hi => GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hi
  obtain ⟨u, hu⟩ : IsUnit (Formalism.L2.Theta.mt V g).det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨(matHom V g), rfl⟩
  have k1 : (e * (u : AE D) + (1 - e)) * (e * (u⁻¹ : (AE D)ˣ) + (1 - e)) = 1 := by
    have := u.mul_inv
    linear_combination (e * e) * this + ((2 : AE D) - u - (u⁻¹ : (AE D)ˣ)) * he
  exact ⟨⟨_, _, k1, (mul_comm _ _).trans k1⟩, by rw [IsDetAt, ← hu]⟩

theorem exists_point {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (hA : l.A = 1)
    (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hmk : ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧
      ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1))
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (hD : Dom a V.rank) (mu : GA D W → ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cst : U.Comp → ℂ)
    (hcc : CcIs θ V W hr U dict mu x₀ om f₀ cst) (h : GA D W) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (Dc : Dic Dw c σ (U.X (dict h).1) g Dw.p V.rank a) (γ : GA D W)
      (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (v : TF V.rank g) (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ)
      (B : AnFib (U.X (dict h).1) Dc.bas Dc.idx Dc.e (dict h).2 (U.X (dict h).1).Λ
        (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict h).1 ⟨(dict h).2, hx⟩)),
      AtComp θ W hr U.X dict x₀ h γ ∧ SelfD (U.X (dict h).1) (U.X (dict h).1).Λ ∧ IsMark l (U.X (dict h).1).Λ mk ∧
      B.Marked mk ∧ MarkAd l W hr ι (γ * h) mk ∧
      B.Reads 1 (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict h).1 ⟨(dict h).2, hx⟩).s ϑ ∧
      IsVac (U.X (dict h).1) Dc.bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) (U.X (dict h).1).Λ) v ∧
      (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA (U.X (dict h).1) Dc.bas Dc.idx v (dict h).2 z) ∧
      Reads θ V W hr (U.X (dict h).1) Dc.bas Dc.idx (om (1, γ * h) f₀) ((cst (dict h).1 * mu h * κ') • v) (dict h).2 := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Wt⟩ := nonempty_uw (U := Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨hon, γ, hat, hma⟩ := hmk Wt h
  have hn : Even V.rank := hD.2
  obtain ⟨-, hsd, hmark, -⟩ := uw_lattice _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU h1 Wt (dict h).1
  obtain ⟨Dc, hDe, -⟩ := exists_dic _ H Dw l c σ r Wt.g V.rank (U.X (dict h).1) a Wt.e hσ hU.1 (hU.2.1 _).1 (hU.2.1 _).2 hsd hD
  obtain ⟨hx, hux, -⟩ := hx_of_isONFr _ r Wt.g V.rank _ Dc.bas Dc.idx Dc.sympl hn _ hon
  have hw : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset V.rank 1)).1
  have key := uw_anFib _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU h1 Wt (dict h).1 Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx⟩ hux
  rw [← hDe] at key
  obtain ⟨B, hBm, ϑ, hϑ, -⟩ := key
  have hT := isTheta1_of_reads_generator _ H Dw l Xo c _ _ _ Dc.bas Dc.idx Dc.e _ _ _ B Dc.sympl hx hsd ϑ hϑ
  obtain ⟨κ', hκ⟩ := VacProd.prod_eq_mul_thA _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hn _ hw hw' _ hsd v hv _ hx ϑ hT
  refine ⟨hx, Wt.g, Dc, γ, Wt.mark (dict h).1, v, ϑ, κ', B, hat, hsd, hmark, hBm, hma, hϑ, hv, hκ, ?_⟩
  obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ r Wt.g V.rank _ Dc.bas Dc.idx Dc.sympl hn _ hx v hv.1).2.2 v hv.1).1
    (cst (dict h).1 * mu h * κ') 0
  rw [zero_smul, add_zero] at s1 s2
  rw [zero_smul, add_zero] at s2
  refine ⟨s1, fun w hw0 => ?_⟩
  rw [hcc.2 h γ hat hx Wt.g Dc.bas Dc.idx Dc.e Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ ϑ ⟨B, hϑ⟩ w hw0, hκ, s2, Pi.smul_apply, smul_eq_mul]
  ring

theorem dict_cast {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) ∧
    LatIsom W (T.Q.Dw j).EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) ∧
    (∀ g : GA D W, ∃ x, IsDetRoot W g x) ∧
    ∀ θ : InfFam D, IsInfFam θ → (∀ k, IsMod W hr ((T.U j σ).X k)) → 1 ≤ D.R.r →
      ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))) (h : GA D W),
        IsONFr ((T.U j σ).X (castDict hV (T.dict j σ) h).1) (castDict hV (T.dict j σ) h).2 ∧
        ∃ γ, AtComp θ W hr (T.U j σ).X (castDict hV (T.dict j σ)) (T.x₀ j σ) h γ ∧
          MarkAd T.Q.l W hr (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (γ * h)
            (Wt.mark (castDict hV (T.dict j σ) h).1) := by
  subst hV
  obtain ⟨_, g, e, F, ik, φ, th, h1, h2, h3, h4⟩ := hL.adPin j hj σ hσ
  refine ⟨h1, h2, (hL.muVal j hj σ hσ).1, fun θ hθ hm h0 Wt h => ?_⟩
  obtain ⟨k1, γ, k2, k3, -⟩ := dict_atComp_markAd D _ _ _ _ _ σ _ (T.U j σ) hσ (hL.unf j hj σ hσ) h0 hL.pins.2.1.2 θ _ hr
    (T.dict j σ) _ g e F ik φ th _ hθ hm (hL.familyUniformisationBasePointOrthogonal j hj σ hσ) h3 h4 Wt h
  exact ⟨k1, γ, k2, k3⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

abbrev unfO (O : OMDat T.toCore R i Tp tup) : Unf (T.Q.Xo ((i : ℕ) + 1)) O.c' (inC O.c') D.R.r :=
  unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')


set_option maxHeartbeats 1000000 in
theorem geo_value (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {c0 : ℂ} (hc : CovAt O c0) (t : Tp)
    (X : Data D.host.E D.R.r) (g : ℕ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (k : GA D (Wc D i)) (xk : (AE D)ˣ) (hk : IsDetRoot (Wc D i) k xk) (hX : IsMod (Wc D i) (rank_Wc i) X)
    (hp : X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q) (hpq : (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q)
    (hrk : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) (hn : Even (Vc D i).rank)
    (hΛ : latR (rank_Wc i) (latG (Wc D i) k) = X.Λ) (hsd : SelfD X X.Λ) (x : Frame X.Ψ D.R.r) (hx : x ∈ X.dom)
    (hxk : x = frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1))
    (mk mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (hm : IsMark T.Q.l X.Λ mk)
    (hm₂ : IsMark (O.dδ t).l₂ X.Λ mk₂) (ha₂ : MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk₂)
    (hov : MarkOver T.Q.l (O.dδ t).l₂ X.Λ mk mk₂) (v : TF (Vc D i).rank g) (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ)
    (hv : IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) X.Λ) v)
    (hκ : ∀ z : Fin (Vc D i).rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X Dc.bas Dc.idx v x z)
    (Y : O.Cl' t → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E)
    (hY : ∀ j, IsRoots (O.dδ t).l₂ X.Λ mk₂ (O.Nc t j) (Y j)) (xs : O.Cl' t → VsV D i O.c'.F)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c') (hf : GlobalTheory.OneMapTuples.IsCls O t xs f) :
    letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
    ∀ (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) O.c' ℂ) (B : AnFib X Dc.bas Dc.idx Dc.e x X.Λ y), B.Marked mk → B.Reads 1 y.s ϑ →
      evR (T.Q.Xo ((i : ℕ) + 1)) O.c' f y = c0 * ((R.xi (tup t) xk : Circle) : ℂ) * κ' *
        clsSum (inC O.c') X Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t)
          (fun j => O.io (xs j)) X.Λ v Y x := by
  letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
  letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra
  intro y B hB hϑ
  have halg : ∀ s : O.c'.F, algebraMap (O.dδ t).c₂.F ℂ ((O.dδ t).eF s) = algebraMap O.c'.F ℂ s := fun s => rfl
  obtain ⟨hlev, hA₂, hnab⟩ := hP.cov t
  obtain ⟨y₂, B₂, hov₂, hB₂, hrd⟩ := MarkLift.exists_lift_marked _ _ _ _ _ O.c' _ (O.dδ t) halg hlev hT.laws.pins.2.1.2 hA₂
    (fun h => absurd h hpq) _ g X Dc.bas Dc.idx Dc.e x X.Λ y B Dc.sympl hx hsd mk mk₂ hm hB hm₂ hov
  obtain ⟨-, cga, hio⟩ := hP.io
  have h1 := evR_eq_clsSum GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ t) halg hnab _ g X Dc.bas Dc.idx Dc.e x X.Λ y y₂ B₂ hov₂
    Dc.sympl hx hsd _ Dc.hr Dc.eL hrk hn Dc.dir_eq ϑ v κ' (hrd ϑ hϑ) hv hκ mk₂ hm₂ hB₂ (O.Cl' t) (O.w t) (O.La t) (O.Nc t)
    (O.gam t) (O.vol t) (O.ep t) _ O.io xs (wtA (κ i))
    (fun j => ⟨((hP.reps t).1 j).1, ((hP.reps t).1 j).2.2.1, ((hP.reps t).1 j).2.2.2.1⟩)
    (fun j => mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self _ _)) Y hY f hf
  subst hxk
  rw [h1, hc t X g Dc.bas Dc.idx Dc.e k xk mk₂ hX hp Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ hΛ hk hm₂ ha₂ y₂ B₂ hB₂]
  rfl

end GlobalTheory.PtId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionOntoFiniteGroupSurjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

set_option maxHeartbeats 1000000 in
theorem redQ_surjective : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U), Function.Surjective (LiftBrg.ActQ.redQ X I U L eG i t) := by
  intro X px I U L eG _ _ hL _ i t g
  obtain ⟨c, hc⟩ := hL.is.βV i
  obtain ⟨κ, -, hpar, hr⟩ := GlobalTheory.ParahoricLift.liftsExist (Vc X.toD7 i) (L.βV i) (L.datVt i t) _ _ hc
    (GlobalTheory.StepLifts.places_apart L hL.is t).1 (GlobalTheory.StepLifts.places_apart L hL.is t).2 (eG g)
  refine ⟨⟨(finHom (Vc X.toD7 i)).rangeRestrict κ, ⟨hpar, Subgroup.mem_top _⟩⟩, ?_⟩
  rw [redQ_apply]
  show eG.symm (rTup (L.βV i) (L.datVt i t) (finE (Vc X.toD7 i) κ)) = g
  rw [hr, MulEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  first | exact @GlobalTheory.TiePlace.place_of_tie | exact GlobalTheory.TiePlace.place_of_tie | (intros; apply GlobalTheory.TiePlace.place_of_tie <;> assumption)
end

