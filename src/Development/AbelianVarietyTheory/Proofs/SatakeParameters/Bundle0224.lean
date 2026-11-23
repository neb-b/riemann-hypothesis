module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectors
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocal

open GlobalTheory.PRep

theorem exists_trivOutside_map_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (h : GL (Fin n) (s.w.adicCompletion L)) :
    ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h := by
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  refine ⟨x, hx, ?_⟩
  rw [e]
  ext i j
  simp

theorem exists_eigen_of_sum {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V) (hf0 : ∑ i, T i (y i) ≠ 0)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h ∈ K, ρ h v = θ h • v :=
  _root_.GlobalTheory.ExistsEigenvector.exists_eigenvector hρ hK hU h1 θ hθU hmul T y hf0 hinv

set_option maxHeartbeats 1000000 in
theorem exists_eigen_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ), K ≤ KO (s.w.adicCompletion L) (Fin n) → (∀ h ∈ KOne (s.w.adicCompletion L) (Fin n), h ∈ K ∧ θ h = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∃ y : σ.V, y ≠ 0 ∧ ∀ h ∈ K, σ.ρ h y = θ h • y := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ hK hKOne f hf hf0 hθ
  classical
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := exists_trivOutside_map_loc n s c h
    exact ⟨x, hx, e, by rw [hθ x hx (e ▸ hh), e]⟩
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, θ (k * k') = θ k * θ k' := by
    intro k hk k' hk'
    obtain ⟨x, hx, e, hfx⟩ := hrt k hk
    obtain ⟨x', hx', e', hfx'⟩ := hrt k' hk'
    have hxx : TrivOutside {s.v} (x * x') := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hx'
    have e2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (x * x')) = k * k' := by
      rw [map_mul, map_mul, e, e']
    have h2 := hθ (x * x') hxx (e2 ▸ mul_mem hk hk')
    rw [e2] at h2
    have h3 : NG.rt L n (x * x') f = NG.rt L n x (NG.rt L n x' f) := by
      funext g; simp [NG.rt, mul_assoc]
    rw [h3, hfx', map_smul, hfx, smul_smul] at h2
    have h4 : (θ (k * k') - θ k' * θ k) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · rw [sub_eq_zero.1 h5, mul_comm]
    · exact absurd h5 hf0
  have hmem := _root_.GlobalTheory.SpanLoc.main L n a S hS s σ hloc c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose y hy using fun i => LinearMap.mem_range.1 (hF i)
  have hsum : ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1) = f := by
    rw [← hFsum, Finsupp.sum, ← Finset.sum_attach F.support]
    exact Finset.sum_congr rfl fun j _ => hy j.1
  have hKo : IsOpen (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    Subgroup.isOpen_mono (fun h hh => (hKOne h hh).1) GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  refine exists_eigen_of_sum σ.smooth hKc GlobalTheory.StepData.isOpen_KOne (one_mem _) θ
    (fun g hg _ => (hKOne g hg).2) hmul (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)))
    (fun j => y j.1) (by rw [hsum]; exact hf0) ?_
  intro k hk
  obtain ⟨x, hx, e, hfx⟩ := hrt k hk
  subst e
  have hj : ∀ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
      (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (y j.1)) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1)) := fun j => j.1.2.2 x hx (y j.1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl fun j _ => hj j, ← map_sum, hsum, hfx]

end GlobalTheory.EigLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairReadPf

theorem exists_splitPlace_w (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  have hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun _ =>
    D.host.φ₀.injective (by
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
  obtain ⟨x0, hx0, hx0'⟩ := hw
  have hc0 : IsCMField.ringOfIntegersComplexConj D.host.E x0 ∉ w.asIdeal :=
    hx0' _ (by rw [hstar, IsCMField.coe_ringOfIntegersComplexConj])
  obtain ⟨s, hs⟩ := GlobalTheory.SplitConjPlace.exists_splitPlace w x0 hx0 hc0
  have hsw : s.w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [s.w_under, hs]; rfl
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w s.w hsw with h | h
  · exact ⟨s, h⟩
  · refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
    rw [GlobalTheory.SplitConjPlace.mem_conj_w, h, GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]

theorem exists_ne_of_mem_iSup {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (p : ι → Submodule ℂ M)
    (ℓ : M →+ ℂ) {x : M} (hx : x ∈ ⨆ i, p i) (h : ℓ x ≠ 0) : ∃ i, ∃ y ∈ p i, ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  exact h (Submodule.iSup_induction p (motive := fun z => ℓ z = 0) hx (fun i y hy => H i y hy) (map_zero ℓ)
    (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]))

theorem exists_ne_of_mem_iSup_sub {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (A : Submodule ℂ M)
    (p : ι → Submodule ℂ M) (hpA : ∀ i, p i ≤ A) (ℓ : A →+ ℂ) (x : A) (hx : (x : M) ∈ ⨆ i, p i)
    (h : ℓ x ≠ 0) : ∃ i, ∃ y : A, (y : M) ∈ p i ∧ ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨_, hk⟩ := Submodule.iSup_induction p (motive := fun z => ∃ hz : z ∈ A, ℓ ⟨z, hz⟩ = 0) hx
    (fun i y hy => ⟨hpA i hy, H i ⟨y, hpA i hy⟩ hy⟩) ⟨A.zero_mem, by exact map_zero ℓ⟩
    (fun a b ⟨ha, ea⟩ ⟨hb, eb⟩ => ⟨A.add_mem ha hb, by
        have e : (⟨a + b, A.add_mem ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [e, map_add (f := _), ea, eb, add_zero]⟩)
  exact h hk

def precompₛ {V C : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup C] [Module ℂ C] (T : V →ₗ[ℂ] C) :
    (C →ₗ⋆[ℂ] ℂ) →ₗ[ℂ] (V →ₗ⋆[ℂ] ℂ) where
  toFun f := f.comp T
  map_add' f g := by ext; rfl
  map_smul' a f := by ext; rfl

end GlobalTheory.PairReadPf


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSplitTrivOutsideAndAtPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CongSplitBoth

open GlobalTheory.IdemSplit GlobalTheory.CongSplit

theorem split_cong_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n), NG.Cong L n N κ → ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ NG.Cong L n N x ∧ NG.Cong L n N y ∧ κ = x * y := by
  intro L _ _ _ n N v κ hc
  set e := idemAt L v with he_def
  have he : e * e = e := idemAt_mul_self L v
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hσ : conjAL L e = e := conjAL_idemAt L v
  have hσ' : conjAL L (1 - e) = 1 - e := by rw [map_sub, map_one, hσ]
  have hei : e ∈ ALint L := idemAt_mem L v
  have hei' : 1 - e ∈ ALint L := Subring.sub_mem _ (one_mem _) hei
  refine ⟨gaFold he hσ κ, gaFold he' hσ' κ, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ v := by simpa using hw
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_idemAt_ne L v hw', compAt_one_apply]
    simp
  · intro w hw
    have hw' : w = v := by simpa using hw
    subst hw'
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_one_apply]
    simp [he_def, compAt_idemAt_self]
  · refine ⟨gaFold_mem_Umax L he hσ hei κ hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨e * y, Subring.mul_mem _ hei hy, ?_⟩
    rw [gaFold_val, fold_apply]
    linear_combination e * hEq
  · refine ⟨gaFold_mem_Umax L he' hσ' hei' κ hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨(1 - e) * y, Subring.mul_mem _ hei' hy, ?_⟩
    rw [gaFold_val, fold_apply, sub_sub_cancel]
    linear_combination (1 - e) * hEq
  · apply Subtype.ext; apply Units.ext
    show (κ.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e _ * fold (1 - e) _
    rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.CongSplitBoth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcrete
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.AtG

theorem ramCols_true : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), ∃ eM : ((I.rec7 l Z).div.Nu u).V ≃+ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, (∀ (r : (I.rec7 l Z).what₂.LL) x, eM (r • x) = (show B.fields.K from r) • eM x) ∧ (∀ x, x ∈ DV.MramL (I.rec7 l Z) u ↔ eM x ∈ Formalism.L2.Col.MramL (Pr := B.primes X) B.wts I.Ch u) ∧ (∀ x, (I.rec7 l Z).nuIn u x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (eM x).1) ∧ ∀ a φ, (I.fm l u a).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ)) := by
  intro B X I h l Z l0 u
  have hX := (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1
  obtain ⟨κ, hκ⟩ := GlobalTheory.Core.ColZero.exists_colEquiv I h hX l u I.mu0
  have hκc : ∀ φ, κ φ = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ := fun φ => Subtype.ext (funext (hκ φ))
  have hram : ∀ φ, κ φ ∈ (I.fm l u I.mu0).ramSub ↔ φ ∈ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u := fun φ =>
    GlobalTheory.Core.ColRam.isCol_mem_ramSub_iff I h hX l u I.mu0 (κ φ) φ (hκ φ)
  have hrange : ∀ x, (I.rec7 l Z).nuIn u x ∈ (I.fm l u I.mu0).ramSub := fun x =>
    (I.rec7 l Z).nuIn_range u ▸ ⟨x, rfl⟩
  have hinj := (I.rec7 l Z).nuIn_inj u
  have hsurj : ∀ φ : Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, ∃ x, (I.rec7 l Z).nuIn u x = κ φ.1 := by
    intro φ
    have hm : κ φ.1 ∈ LinearMap.range ((I.rec7 l Z).nuIn u) := (I.rec7 l Z).nuIn_range u ▸ (hram φ.1).2 φ.2
    exact hm
  let f : ((I.rec7 l Z).div.Nu u).V → Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u := fun x =>
    ⟨κ.symm ((I.rec7 l Z).nuIn u x), (hram _).1 (Eq.subst (motive := fun y => y ∈ (I.fm l u I.mu0).ramSub) (κ.apply_symm_apply ((I.rec7 l Z).nuIn u x)).symm (hrange x))⟩
  have hf : ∀ x, κ (f x).1 = (I.rec7 l Z).nuIn u x := fun x => κ.apply_symm_apply _
  have fbij : Function.Bijective f := by
    refine ⟨fun x y e => hinj ?_, fun φ => ?_⟩
    · rw [← hf x, ← hf y, e]
    · obtain ⟨x, hx⟩ := hsurj φ
      exact ⟨x, Subtype.ext (by rw [← κ.injective.eq_iff, hf, hx])⟩
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y => Subtype.ext (by
    exact (congrArg κ.symm (map_add ((I.rec7 l Z).nuIn u) x y)).trans (map_add κ.symm _ _))
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) fbij, ?_, ?_, ?_, ?_⟩
  · intro r x
    apply Subtype.ext
    show κ.symm _ = _
    exact (congrArg κ.symm (map_smul ((I.rec7 l Z).nuIn u) r x)).trans (map_smul κ.symm _ _)
  · intro x
    have e := GlobalTheory.Core.Ht2.colStep0_mem_lat I h hX l u I.mu0 (κ (f x).1) (f x).1 (hκ _)
    show (I.rec7 l Z).nuIn u x ∈ ((I.fm l u I.mu0).lat 0).L ↔ (f x).1 ∈ Formalism.L2.Col.MfL (Pr := B.primes X) B.wts I.Ch u
    exact (Eq.subst (motive := fun y => (y ∈ ((I.fm l u I.mu0).lat 0).L ↔ (f x).1 ∈ Formalism.L2.Col.MfL (Pr := B.primes X) B.wts I.Ch u)) (hf x) e)
  · intro x
    show _ = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (f x).1
    rw [← hκc, hf]
  · intro a φ
    funext c'
    have e := GlobalTheory.LvT.TrueStep0.rep_eCls0_symm h l u a c'
    show Formalism.L2.Col.evV _ _ _ _ (φ.1 ((I.stp u a 0).rep c').1.1.deco) =
      Formalism.L2.Col.evV _ _ _ _ (φ.1 ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm c')).1.1.deco)
    rw [e]

end GlobalTheory.AtG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarIsotypic
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut

noncomputable section

namespace GlobalTheory.SumTransIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem sumRt_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (Formalism.AUTREP.GAf L n → W)}
    (hS : Formalism.L2.NG.IsSubrep ρ S) (hiso : Formalism.L2.NG.IsoRep S S')
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f)
    (f' : Formalism.AUTREP.GAf L n → W) (hf' : f' ∈ S')
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f' = f') :
    ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f' = c • f' := by
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : Formalism.AUTREP.GAf L n,
      ((T ⟨Formalism.L2.NG.rt L n h f, hS.stable h _ f.2⟩ : S') : Formalism.AUTREP.GAf L n → W) = Formalism.L2.NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ (f : Formalism.AUTREP.GAf L n → W) = f := by
    intro κ hκ ht
    have h1 := hrt κ
    rw [hfix κ hκ ht] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ γ ∈ R, (⟨Formalism.L2.NG.rt L n (r γ) f, hS.stable _ _ f.2⟩ : S)
  have hσ : (σ : Formalism.AUTREP.GAf L n → W) = ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f := by
    simp only [σ, Submodule.coe_sum]
  have hTσ : ((T σ : S') : Formalism.AUTREP.GAf L n → W) = ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f' := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [σ, map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ => hrt _
  have key : σ = c • f := Subtype.ext (by rw [hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : Formalism.AUTREP.GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

theorem iSup_finset_stable (t : Finset (Submodule ℂ (Formalism.AUTREP.GAf L n → W)))
    (ht : ∀ i ∈ t, ∀ h, ∀ f ∈ i, Formalism.L2.NG.rt L n h f ∈ i) (h : Formalism.AUTREP.GAf L n) :
    ∀ f ∈ (⨆ i ∈ t, i), Formalism.L2.NG.rt L n h f ∈ (⨆ i ∈ t, i) := by
  have hle : (⨆ i ∈ t, i) ≤ (⨆ i ∈ t, i).comap (Formalism.L2.NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ t) => i) i hi) (ht i hi h f hf)
  exact fun f hf => hle hf

theorem sumRt_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (Formalism.AUTREP.GAf L n → W)}
    (hS : Formalism.L2.NG.IsIrrRep ρ S)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f)
    (t : Finset (Submodule ℂ (Formalism.AUTREP.GAf L n → W))) :
    ((↑t : Set (Submodule ℂ (Formalism.AUTREP.GAf L n → W))) ⊆ {S' | Formalism.L2.NG.IsIrrRep ρ S' ∧ Formalism.L2.NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : Formalism.L2.NG.IsIrrRep ρ a ∧ Formalism.L2.NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | Formalism.L2.NG.IsIrrRep ρ S' ∧ Formalism.L2.NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), Formalism.L2.NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      iSup_finset_stable t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : Formalism.L2.NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _)] at e
        have hd : Formalism.L2.NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : Formalism.L2.NG.rt L n κ y - y = z - Formalism.L2.NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _), hyfix κ hκ hκt] at e
        exact add_left_cancel e
      have e1 := sumRt_iso hS.1 haF.2 v R r c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [map_add (f := _), Finset.sum_add_distrib, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

theorem sumRt_isoTyp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n)
    (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S →
    ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ),
    (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) →
    ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS v ι R r c hc f hf hfix
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact sumRt_finset_sum hS v R r c hc t ht f hft hfix

end GlobalTheory.SumTransIso
end
end

