module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLeviBlockEigenvectorAtIdentity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open Matrix ValuativeRel

noncomputable section

namespace GlobalTheory.SphBlock

theorem exists_eigen_at_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ) (x : IndSp e (piTensor σ)), x ≠ 0 → (∀ g ∈ KO k n, multiProd e σ g x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → ∃ w : PiTensorProduct ℂ X, w ≠ 0 ∧ ∀ a, ∀ h ∈ KO k (m a), piTensor σ (Pi.mulSingle a h) w = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • w := by
  intro k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ σ χ x hx hK
  classical
  set f := x.1.1 with hf
  have hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {g : GL d k}, g ∈ KO k d →
      valuation k (GeneralLinearGroup.det g : k) = 1 := by
    intro d _ _ g hg
    obtain ⟨g, rfl⟩ := hg
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
        algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  have hfK : ∀ κ ∈ KO k n, f κ = (χ (GeneralLinearGroup.det κ) : ℂ) • f 1 := by
    intro κ hκ
    have h := congrArg (fun y : IndSp e (piTensor σ) => y.1.1 1) (hK κ hκ)
    have h2 : (multiProd e σ κ x).1.1 1 = f (1 * κ) := parInd_apply e (piTensor σ) κ 1 x
    rw [h2, one_mul] at h
    exact h
  refine ⟨f 1, ?_, ?_⟩
  · intro h0
    apply hx
    have hall : ∀ g, f g = 0 := by
      intro g
      obtain ⟨u, l, κ, hκ, rfl⟩ := UnitInd.exists_iwasawa e g
      let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
        mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
      have := parInd_law e (piTensor σ) x p κ
      change f ((u : GL n k) * leviEmb k e l * κ) = _ at this
      rw [this, show x.1.1 κ = f κ from rfl, hfK κ hκ, h0, smul_zero, map_zero, smul_zero]
    apply Subtype.ext; apply Subtype.ext; funext g
    exact hall g
  · intro a h hh
    set l : Levi k m := Pi.mulSingle a h with hl
    have hlK : ∀ b, l b ∈ KO k (m b) := by
      intro b
      by_cases hb : b = a
      · subst hb; simp [l, hh]
      · simp [l, Pi.mulSingle_eq_of_ne hb, one_mem]
    have hemb : leviEmb k e l ∈ KO k n := by
      have := (UnitInd.unip_mul_levi_mem_KO e (1 : unipRad k e) l).2 ⟨one_mem _, hlK⟩
      simpa using this
    have hdet : GeneralLinearGroup.det (leviEmb k e l) = GeneralLinearGroup.det h := by
      rw [det_leviEmb, Finset.prod_eq_single a]
      · simp [l]
      · intro b _ hb; simp [l, Pi.mulSingle_eq_of_ne hb]
      · simp
    have hδ : deltaHalf k m l = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one fun b _ => isUnram_absPow k _ _ (hval (hlK b))
    let p : parab k e := ⟨leviEmb k e l, leviEmb_mem_parab k e l⟩
    have hlaw := parInd_law e (piTensor σ) x p 1
    have hp : leviProj k e p = l := leviProj_leviEmb k e l
    rw [mul_one, hp, hδ, Units.val_one, one_smul] at hlaw
    change f (leviEmb k e l) = piTensor σ l (f 1) at hlaw
    rw [hfK _ hemb, hdet] at hlaw
    exact hlaw.symm

end GlobalTheory.SphBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldPlaceInRamifiedSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeoUnder

theorem exists_under_in_qPl : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  intro D χ w hg hχ
  have hne : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (hint.tower_top)
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := hne }
  refine ⟨v, rfl, ?_, w, rfl, hχ⟩
  rintro ⟨w', hw', k, hk⟩
  apply hg k
  have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw']
    show algebraMap _ _ _ ∈ w'.asIdeal
    rw [map_natCast]; exact hk
  show ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  have h2 := h1
  change algebraMap _ _ _ ∈ w.asIdeal at h2
  rwa [map_natCast] at h2

end GlobalTheory.GeoUnder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfIsoSplitPlaceComponents
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocSplitGraph

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (s : SplitPlace L) (σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S₁ s σ₁ → IsLocS S₂ s σ₂ → Nonempty (σ₁.ρ.Equiv σ₂.ρ) → ∃ X : Submodule ℂ ((GAf L n → a.W) × (GAf L n → a.W)), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂) ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ z ∈ X, (NG.rt L n x z.1, NG.rt L n x z.2) ∈ X) ∧ (∀ u, ((0 : GAf L n → a.W), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : GAf L n → a.W)) ∈ X → u = 0) := by
  intro L _ _ _ n a S₁ S₂ s σ₁ σ₂ h₁ h₂ hE
  obtain ⟨E⟩ := hE
  obtain ⟨i₁, T₁, hi₁, hiL₁, hT₁inj, hT₁S, hT₁eq⟩ := h₁
  obtain ⟨i₂, T₂, hi₂, hiL₂, hT₂inj, hT₂S, hT₂eq⟩ := h₂

  have hci : i₁ = i₂ := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (i₁ : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i₂ := by
      refine hd.equalizer hi₁ hi₂ (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hiL₁, hiL₂]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  let F : σ₁.V →ₗ[ℂ] (GAf L n → a.W) × (GAf L n → a.W) := T₁.prod (T₂ ∘ₗ E.toLinearEquiv.toLinearMap)
  have hF : ∀ u, F u = (T₁ u, T₂ (E u)) := fun u => rfl
  have hEint : ∀ g u, E (σ₁.ρ g u) = σ₂.ρ g (E u) := fun g u => LinearMap.congr_fun (E.isIntertwining' g) u
  have hnt : Nontrivial σ₁.V := by
    haveI := σ₁.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ₁.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ₁.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  refine ⟨LinearMap.range F, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := exists_ne (0 : σ₁.V)
    intro h
    have hm : F u ∈ LinearMap.range F := ⟨u, rfl⟩
    rw [h, Submodule.mem_bot, hF, Prod.mk_eq_zero] at hm
    exact hu (hT₁inj (hm.1.trans (map_zero T₁).symm))
  · rintro _ ⟨u, rfl⟩
    exact ⟨hT₁S u, hT₂S (E u)⟩
  · rintro x hx _ ⟨u, rfl⟩
    refine ⟨σ₁.ρ (Matrix.GeneralLinearGroup.map i₁.toRingHom (s.loc n x)) u, ?_⟩
    rw [hF, hF, hT₁eq x hx u, hEint, hT₂eq x hx (E u)]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : v = 0 := hT₁inj (hv.1.trans (map_zero T₁).symm)
    rw [← hv.2, hv0, map_zero, map_zero]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : E v = 0 := hT₂inj (hv.2.trans (map_zero T₂).symm)
    have : v = 0 := by simpa using hv0
    rw [← hv.1, this, map_zero]

end GlobalTheory.LocSplitGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GoodCuspPoint

theorem param_parts_pos_rank (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (hx : HasParamX D.nd D.naut i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso D.nd D.naut Sig = D.R.r := by
  obtain ⟨P, -, hBC⟩ := hx
  refine ⟨fun p hp => ?_, ?_⟩
  · have hm : (⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ : Formalism.BasicNotions.Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
      List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
    exact ⟨(hBC.1 _ hm).1, (hBC.1 _ hm).2.1⟩
  · have h := hBC.2.2.1
    have e : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) =
        rankIso D.nd D.naut Sig + D.R.t := by
      simp [rankIso, twistIso, muPart, List.map_map, Function.comp_def]
    rw [e] at h
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

theorem cuspidal_of_good_labels (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tieLab D) (i : D.nd.Loc) (x : D.nd.X i)
    (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (hx : HasParamX D.nd D.naut i x Sig)
    (hg : goodSig D.nd D.naut Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨hpos, hrank⟩ := param_parts_pos_rank D i x Sig hx
  let k : Fin 2 := 0
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := (hg k).1
  have : Nonempty (D.nd.PlG k) := by
    rw [← Fintype.card_pos_iff, D.nd.card_PlG k]
    show 0 < 2 * D.R.ord
    have := D.R.ord_pos
    omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  have hf : ∀ v, D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) =
      ∏ j : Fin Sig.length,
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d := by
    intro v
    rw [Formalism.MainNotions.SumRepresentations.inertiaCharpoly_eq_of_iso D.nd D.naut hT k v Sig,
      Formalism.MainNotions.SumRepresentations.list_prod_fin Sig (fun p => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d)]
  have hrk : ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d = D.R.r := by
    rw [← hrank, rankIso, Formalism.MainNotions.SumRepresentations.list_sum_fin Sig (fun p => p.a * p.d)]
  have hd : ∀ j : Fin Sig.length, 1 ≤ (Sig.get j).a ∧ 1 ≤ (Sig.get j).d :=
    fun j => hpos _ (List.get_mem Sig j)
  have hdeg : ∀ v (j : Fin Sig.length),
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree =
        (Sig.get j).a := by
    intro v
    have hne : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hf v]
      exact (h1 v).1.ne_zero
    have hsum : ∑ j : Fin Sig.length,
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d =
        ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d := by
      have h1' : (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r :=
        (h1 v).2.1
      rw [hrk, ← h1', hf v, natDegree_prod _ _ hne]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, mul_comm]
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d ≤ (Sig.get j).a * (Sig.get j).d := by
      intro j _
      refine Nat.mul_le_mul_right _ ?_
      have := hT.2 k v (D.naut.locG (Sig.get j).π (D.naut.plGw k v))
      rwa [D.naut.locG_dim] at this
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)
    exact Nat.eq_of_mul_eq_mul_right (hd j).2 this
  obtain ⟨hc, hall⟩ := Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one (ZMod (D.host.g k)) (D.nd.PlG k) D.R.r
    (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
    (Fin Sig.length) (fun j => (Sig.get j).a) (fun j => (Sig.get j).d)
    (fun v j => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))) hr
    (fun v => (h1 v).2.1) h2 hf hdeg (fun j => (hd j).1) (fun j => (hd j).2)
    (by
      rintro ⟨a, ha1, ha2, ha⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (ha v))
  rw [Fintype.card_fin] at hc
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hc
  obtain ⟨hd1, ha1⟩ := hall ⟨0, by simp⟩
  obtain ⟨a, π, d⟩ := p
  simp only [List.get_eq_getElem, List.getElem_cons_zero] at hd1 ha1
  subst hd1 ha1
  exact ⟨π, rfl⟩

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tieLab D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut :=
  fun D hT i x Sig hx hg => cuspidal_of_good_labels D hT i x Sig hx hg

end GlobalTheory.GoodCuspPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeComp

theorem smooth_loc {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := by
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ w
  have hu := unif_spec w
  set c : w.adicCompletion E := ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ (n + 1) with hc
  have hv : Valued.v c = WithZero.exp (-((n : ℤ) + 1)) := by
    unfold IsUnifAt at hu
    rw [hc, map_pow, hu, ← WithZero.exp_nsmul]; congr 1; simp
  have ho : IsOpen {x : (w.adicCompletion E)ˣ | ((x : w.adicCompletion E) - 1) * c⁻¹ ∈ w.adicCompletionIntegers E} :=
    (Valued.isOpen_valuationSubring _).preimage ((Units.continuous_val.sub continuous_const).mul continuous_const)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  have h1 : Valued.v (((x : w.adicCompletion E) - 1) * c⁻¹) ≤ 1 := hx
  rw [map_mul, map_inv₀, hv, mul_inv_le_iff₀ WithZero.exp_pos, one_mul] at h1
  have h2 : Valued.v ((x : w.adicCompletion E) - 1) < 1 :=
    h1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  refine hn x ?_ (h1.trans (WithZero.exp_le_exp.2 (by omega)))
  have := Valuation.map_one_add_of_lt _ h2
  rwa [add_sub_cancel] at this

theorem eq_of_isComp {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {ξ ξ' : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : IsComp χ w ξ) (hξ' : IsComp χ w ξ') : ξ' = ξ := by
  have hs := hξ'.1.mul hξ.1.inv
  have hc := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 (MonoidHom.ext fun y => ?_)
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hc.isOpen_compl
  have hyU : (y : w.adicCompletion E) ∈ U := by
    have : y ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨y, hyU, y.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  show ξ' _ * (ξ _)⁻¹ = 1
  rw [hξ.2, hξ'.2]
  exact mul_inv_cancel _

theorem main : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)), ∃ ξ, IsComp χ w ξ ∧ (∀ ξ', IsComp χ w ξ' → ξ' = ξ) ∧ (χ.IsUnitary → ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1) := by
  intro E _ _ χ w
  have hc : IsComp χ w (χ.loc w) := ⟨smooth_loc χ w, fun _ => rfl⟩
  exact ⟨χ.loc w, hc, fun ξ' h' => eq_of_isComp hc h', fun hu x => hu _⟩

end GlobalTheory.HeckeComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleGl1IsoDet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLOneChar

open GlobalTheory.SmGL

theorem equiv_detRep_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  intro k _ _ _ _ d V _ _ σ ω hd hirr hω
  have hact : ∀ (g : GL (Fin d) k) (v : V), σ g v = (ω (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro g v
    conv_lhs => rw [GlobalTheory.ProdSupport.eq_scalar_det hd g]
    exact hω _ v
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : (⊥ : Subrepresentation σ) = ⊤ :=
      Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g w hw => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [hact, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩
  have hS : S = ⊤ := by
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact hv this
    · exact h
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℂ V v) := by
    intro w
    have hw : w ∈ S.toSubmodule := by rw [hS]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨c, rfl⟩
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℂ V v) := by
    intro a b hab
    simp only [LinearMap.toSpanSingleton_apply] at hab
    exact smul_left_injective ℂ hv hab
  let e : ℂ ≃ₗ[ℂ] V := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨(Representation.Equiv.mk e fun g => ?_).symm⟩
  ext c
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, detRep, ofChar_apply,
    detChar_apply, hact, smul_smul, smul_eq_mul]
  rw [mul_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one]

end GlobalTheory.GLOneChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwistParamAbove

theorem isFrobSS_wdRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    IsFrobSS (wdRho P ι Bw h hj ρ) (wdN P ι ρ) (wdRep P ι Bw h hj ρ) := by
  obtain ⟨u, hN, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  have := isFrobSS_of_unipotent u hu hc hρ
  rwa [hN] at this

theorem isModel_twist {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω Gw O} {a : ℕ} {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)} {s : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1} (h₁ : IsModel Bw r L s) (h₂ : IsModel Bw c L m) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) := by
  refine ⟨h₁.1, ?_⟩
  rw [← h₁.2, ← h₂.2]
  ext g i j
  simp [mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
  simp [Matrix.map_apply]

end GlobalTheory.TwistParamAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.ParIndSubquot

theorem parInd_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e W W' _ _ _ _ ρ ρ' hρ' h
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι hι).isSmooth hρ'
  have hinj : Function.Injective (parIndMap e ι) := by
    intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hι ?_))
    exact congrFun (congrArg (fun χ : IndSp e ρ' => χ.1.1) hφψ) g
  let σ₀ : Representation ℂ (parab k e) S.toSubmodule := (twist S.toRepresentation (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  have hsurj : Function.Surjective (parIndMap e f) := by
    refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
      hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
      (isSmooth_comp (isSmooth_twist hS (isSmoothChar_deltaHalf k)) _ hcont)
      (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
    intro x _
    refine Submodule.subset_span ⟨(), -x, ?_⟩
    show x = (0 : _) - -x
    simp
  exact (IsSubquotient.of_surjective (parIndMap e f) hsurj).trans (IsSubquotient.of_injective (parIndMap e ι) hinj)

end GlobalTheory.ParIndSubquot
end

