module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0302

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CommutativeHeckeActsByScalarOnFixedVectors
section
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.HeckeScalar

open GlobalTheory.LFun.SatCompare GlobalTheory.LocGL

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {K : Subgroup G}

theorem heckeVec_dosetInd_eq_idem (hπ : GlobalTheory.LGrp.IsIrrSmooth π) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (g : G) {z : V} (hz : z ∈ fixed π K) :
    ∃ N : ℂ, N ≠ 0 ∧ heckeVec π K (dosetInd ℂ K g) z = N • idem hπ.1 hc (π g z) := by
  classical
  have hm := Final.DosetIndMem G K ℂ g
  have hfin := Formalism.UG.P.finite_support_cosets hK hm.2
  have hS : ∀ c : G ⧸ K, c ∈ hfin.toFinset ↔ c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c => by
    simp [dosetInd]
  refine ⟨hfin.toFinset.card, ?_, ?_⟩
  · refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (hS _).2 ?_⟩)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← idem_of_mem hπ.1 hc (heckeVec_mem_fixed hK hm hz), heckeVec,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
      · refine Finset.sum_congr rfl fun c hcS => ?_
        have h1 := (hS c).1 hcS
        obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 h1
        rw [dosetInd, Set.indicator_of_mem h1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
          GlobalTheory.LGrp.mem_fixed.1 hz b hb]
        simpa using idem_apply_mem hπ.1 hc ha (π g z)
      · intro c hc'
        refine Finset.mem_coe.2 ((hS c).2 ?_)
        by_contra h0
        exact hc' (by simp [dosetInd, h0])

theorem exists_scalar : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K →
    (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → GlobalTheory.LGrp.IsIrrSmooth π →
    FiniteDimensional ℂ (fixed π K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  intro G V _ _ _ _ _ π K hc hK hcomm hπ hfd h hh
  by_cases hb : fixed π K = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    have := heckeVec_mem_fixed hK hh hx
    rw [hb] at this
    simpa using this
  haveI : Nontrivial (fixed π K) := Submodule.nontrivial_iff_ne_bot.2 hb
  let A : Module.End ℂ (fixed π K) := (heckeLin hK hh π).restrict fun x hx => heckeVec_mem_fixed hK hh hx
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  obtain ⟨⟨x₀, hx₀⟩, hv⟩ := hcA.exists_hasEigenvector
  have h0 : x₀ ≠ 0 := fun e => hv.2 (Subtype.ext e)
  have he : heckeVec π K h x₀ = c • x₀ := congrArg Subtype.val hv.apply_eq_smul
  have key : ∀ g, heckeLin hK hh π (idem hπ.1 hc (π g x₀)) = c • idem hπ.1 hc (π g x₀) := fun g => by
    obtain ⟨N, hN, e⟩ := heckeVec_dosetInd_eq_idem hπ hc hK g hx₀
    have hm := Final.DosetIndMem G K ℂ g
    refine smul_right_injective V hN ?_
    show N • _ = N • _
    rw [← map_smul, smul_comm N c, ← e, heckeLin_apply, ← heckeVec_conv hK hh hm hx₀, hcomm _ hh _ hm,
      heckeVec_conv hK hm hh hx₀, he, heckeVec_smul hK hm]
  refine ⟨c, fun x hx => ?_⟩
  have all : ∀ w : MonoidAlgebra ℂ G, heckeLin hK hh π (idem hπ.1 hc (orbitMap π x₀ w)) =
      c • idem hπ.1 hc (orbitMap π x₀ w) := fun w => by
    induction w using MonoidAlgebra.induction_on with
    | of g =>
      have : orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀ := by
        show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _
        simp
      rw [this]; exact key g
    | add a b ha hb =>
      have : orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b := map_add _ _ _
      rw [this, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | smul r a ha =>
      have : orbitMap π x₀ (r • a) = r • orbitMap π x₀ a := map_smul _ _ _
      rw [this, map_smul, map_smul, ha, smul_comm]
  obtain ⟨w, rfl⟩ := orbitMap_surjective hπ.2 h0 x
  have := all w
  rwa [idem_of_mem hπ.1 hc hx] at this

end GlobalTheory.LFun.HeckeScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DistributionRelationObj
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution

namespace GlobalTheory.ToricDistributionObj

theorem toricSumFormula_holds : ToricSumFormula :=
  GlobalTheory.ToricSumValue.toricSum_eq exists_isHeckeL_of_hasInf

end GlobalTheory.ToricDistributionObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
section
namespace GlobalTheory.DefiniteDecompObj

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

theorem doubleCosets_mass : ∀ D : D7, DefClassDecomp D :=
  GlobalTheory.DefiniteDecomp.defClassDecomp

end GlobalTheory.DefiniteDecompObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq
section
noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem exists_siegelH_proj_eq (x : ∀ v : HeightOneSpectrum (𝓞 F), siegelH (Fv F v) σ Q)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ∃ p : siegelH (AF F) σ Q,
      (∀ v ∈ S, proj σ Q v p = x v) ∧ (∀ v ∉ S, proj σ Q v p = 1) ∧ ∀ w, projArch σ Q w p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨embP u (x u) * p, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, coe_embP]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [proj_emb_self, h2 _ hu, mul_one]
      · rw [proj_emb_ne σ Q (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [Subgroup.coe_mul, map_mul, coe_embP, proj_emb_ne σ Q hv.1, h2 v hv.2, mul_one]
    · rw [Subgroup.coe_mul, map_mul, coe_embP, projArch_emb, h3, mul_one]

theorem exists_siegelH_projArch_eq (x : ∀ w : InfinitePlace F, siegelH w.Completion σ Q)
    (S : Finset (InfinitePlace F)) : ∃ p : siegelH (AF F) σ Q,
      (∀ w ∈ S, projArch σ Q w p = x w) ∧ (∀ w ∉ S, projArch σ Q w p = 1) ∧ ∀ v, proj σ Q v p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨embArchP u (x u) * p, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, coe_embArchP]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [projArch_embArch_self, h2 _ hu, mul_one]
      · rw [projArch_embArch_ne σ Q (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [Subgroup.coe_mul, map_mul, coe_embArchP, projArch_embArch_ne σ Q hv.1, h2 v hv.2, mul_one]
    · rw [Subgroup.coe_mul, map_mul, coe_embArchP, proj_embArch, h3, mul_one]

variable {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)}

theorem HasIwasawa.adelic (hf : ∀ v : HeightOneSpectrum (𝓞 F), HasIwasawa σ Q (KFin σ Q L v))
    (hi : ∀ w : InfinitePlace F, HasIwasawa σ Q (KArch σ Q w (bc (compInf F E w) a))) :
    HasIwasawa σ Q (KAd σ Q L a) := fun g => by
  choose x k hk hx using fun v => hf v (proj σ Q v g)
  choose y l hl hy using fun w => hi w (projArch σ Q w g)
  have hS := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ Q (sumLat finSumFinEquiv L L) g)
  obtain ⟨p, h1, h2, h3⟩ := exists_siegelH_proj_eq x hS.toFinset
  obtain ⟨q, h4, -, h5⟩ := exists_siegelH_projArch_eq y Finset.univ
  refine ⟨p * q, (↑(p * q) : GAd σ Q)⁻¹ * g, mem_KAd.2 ⟨fun v => ?_, fun w => ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  · rw [map_mul, map_inv, Subgroup.coe_mul, map_mul, h5, mul_one]
    by_cases hv : v ∈ hS.toFinset
    · rw [h1 v hv, hx v, inv_mul_cancel_left]
      exact hk v
    · rw [h2 v hv, inv_one, one_mul]
      exact not_not.1 fun h => hv (hS.mem_toFinset.2 h)
  · rw [map_mul, map_inv, Subgroup.coe_mul, map_mul, h3, one_mul, h4 w (Finset.mem_univ w), hy w, inv_mul_cancel_left]
    exact hl w

end GlobalTheory.Doubling

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev Ser : Type := (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) → GA D (Wc D i) → ℂ

def kernA (t : T0) (h : GA D (Vc D i)) : (R.cV i).W →ₗ[ℂ] Ser R i where
  toFun w v := singleSeries R i (R.ωP i t) (R.vP i t) h ((R.cV i).ρ h⁻¹ w) v
  map_add' w w' := by
    funext v g
    simp [singleSeries, Datum.thetaKO]
  map_smul' c w := by
    funext v g
    simp [singleSeries, Datum.thetaKO]

def kern (t : T0) (h : Bridge.Gf (Vc D i)) : (R.cV i).W →ₗ[ℂ] Ser R i :=
  kernA R i t (MonoidHom.mem_range.1 h.2).choose

def DatumType (t : T0) : Prop :=
  ∀ (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ →
    IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' →
    R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t

def GoodLiftOnto (t : T0) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) : Prop :=
  ∀ θ, OnTies.IsClassSum R i t U ψ ph θ →
    (R.FW i).Wgood U ψ (fun g => (idemOf A.X).coeff g) ≤
      LinearMap.range ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ θ)

end GlobalTheory.TraceIncl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
section
noncomputable section

namespace GlobalTheory.LFun.SplitTie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.LFun.SplitChart
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

section Transport

def glEquiv {A B : Type} [CommRing A] [CommRing B] (n : ℕ) (ψ : A ≃+* B) : GL (Fin n) A ≃* GL (Fin n) B :=
  Units.mapEquiv ψ.mapMatrix.toMulEquiv

variable {ψ : Fv F v ≃+* w.adicCompletion E}

theorem mem_KGL_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (x : GL (Fin n) (Fv F v)) :
    x ∈ KGL v (n := n) ↔ glEquiv n ψ x ∈ KGL w (n := n) := (bc_mem_KGL_iff h3).symm

theorem Tj_comp (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (ϖ : Fv F v) (j : ℕ) :
    Tj ℂ n (Ov E w) (ψ ϖ) j ∘ glEquiv n ψ = Tj ℂ n (Ov F v) ϖ j := by
  have hd : diagJ n (ψ ϖ) j = ψ.mapMatrix (diagJ n ϖ j) := by
    rw [RingEquiv.mapMatrix_apply, diagJ, diagJ, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  have hv : ∀ x : GL (Fin n) (Fv F v), (glEquiv n ψ x).1 = ψ.mapMatrix x.1 := fun _ => rfl
  refine (funext fun g => (Set.indicator_comp_right (g := 1) (glEquiv n ψ)).symm).trans (congrArg (Set.indicator · 1) ?_)
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, (glEquiv n ψ).surjective.exists, ← mem_KGL_iff h3, hd, hv, ← map_mul,
    EmbeddingLike.apply_eq_iff_eq]

theorem isSatVecGL_comp_symm (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (hq : qV E w = qV F v)
    (ρ : Representation ℂ (GL (Fin n) (Fv F v)) V) (x : V) (B : Multiset ℂˣ) :
    IsSatVecGL w (ρ.comp (glEquiv n ψ).symm.toMonoidHom) x B ↔ IsSatVecGL v ρ x B := by
  unfold IsSatVecGL
  rw [mem_fixed_comp_symm (glEquiv n ψ) (mem_KGL_iff h3), hq, ψ.surjective.forall]
  refine and_congr_right fun _ => and_congr_right fun hx => and_congr_right fun _ => forall_congr' fun ϖ => ?_
  have hu : IsUnifV E w (ψ ϖ) ↔ IsUnifV F v ϖ := by unfold IsUnifV; rw [h3]
  rw [hu]
  refine forall_congr' fun hϖ => forall₂_congr fun j _ => ?_
  rw [heckeVec_comp_symm (glEquiv n ψ) (mem_KGL_iff h3) (Tj_mem_hecke (hu.2 hϖ) j).1 hx, Tj_comp h3]

end Transport

variable [Algebra F E] {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}

section Compl

variable (τ : E →ₐ[F] Fv F v) (hw : (splitPrime τ).under (𝓞 F) = v)

theorem complMap_bijective : Function.Bijective (complMap hw) := by
  obtain ⟨ψ, h1, -⟩ := exists_equiv_complMap τ hw
  exact (funext h1 : ⇑ψ = complMap hw) ▸ ψ.bijective

theorem valued_complMap (a : Fv F v) : Valued.v (complMap hw a) = Valued.v a := by
  obtain ⟨ψ, h1, -, h3, -⟩ := exists_equiv_complMap τ hw
  rw [← h1, h3]

theorem complMap_apply_emb (x : E) : complMap hw (τ x) = algebraMap E _ x := by
  obtain ⟨ψ, h1, h2, -⟩ := exists_equiv_complMap τ hw
  rw [← h1, h2]

def complEquiv : Fv F v ≃+* (splitPrime τ).adicCompletion E :=
  RingEquiv.ofBijective (complMap hw) (complMap_bijective τ hw)

theorem complEquiv_apply (a : Fv F v) : complEquiv τ hw a = complMap hw a := rfl

theorem toCompl_eq_complMap (y : Fv F v ⊗[F] E) : toCompl hw y = complMap hw (splitProj τ y) :=
  toCompl_eq (ψ := complEquiv τ hw) (fun _ => rfl) (complMap_apply_emb τ hw) y

theorem qV_splitPrime : qV E (splitPrime τ) = qV F v := absNorm_splitPrime τ

end Compl

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) (hw : (splitPrime τ).under (𝓞 F) = v)
  (β : GL (Fin n) (Fv F v))

variable {τ β}

variable (hL : IsSelfDualAt σ J L v) (hβ : IsSplitBasis τ L β)
include hL hβ

end GlobalTheory.LFun.SplitTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvalues
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LGrp.Zonal

open GlobalTheory.LocGL

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {K : Subgroup G}

theorem heckeVec_dosetInd {σ : Representation ℂ G V} (hσ : IsSmooth σ) (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) {z : V} (hz : z ∈ fixed σ K) (g : G) :
    heckeVec σ K (dosetInd ℂ K g) z =
      ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) • idem hσ hc (σ g z) := by
  have hmem : ∀ c : G ⧸ K, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      c ∈ (P.finite_cosets_in_doset hK g).toFinset := fun c => by
    rw [Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩, fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩⟩
  rw [← idem_of_mem hσ hc (SatCompare.heckeVec_mem_fixed hK (Final.DosetIndMem G K ℂ g) hz)]
  unfold heckeVec
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_support_subset (s := (P.finite_cosets_in_doset hK g).toFinset), map_sum,
    Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
  · refine Finset.sum_congr rfl fun c hc' => ?_
    have h1 := (hmem c).2 hc'
    obtain ⟨a, b, e⟩ := (Set.Finite.mem_toFinset _).1 hc'
    rw [dosetInd, Set.indicator_of_mem h1, Pi.one_apply, one_smul, e, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, mem_fixed.1 hz b b.2, idem_apply_mem hσ hc a.2]
  · intro c hc'
    by_contra h
    exact hc' (by
      show dosetInd ℂ K g c.out • _ = 0
      rw [dosetInd, Set.indicator_of_notMem (fun h' => h ((hmem c).1 h')), zero_smul])


omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem card_ne_zero (hK : IsCommensurated K) (g : G) :
    ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) ≠ 0 := by
  refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (Set.Finite.mem_toFinset _).2 ?_⟩)
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

theorem idem_orbitMap {π : Representation ℂ G V} {ρ : Representation ℂ G W} (hπ : IsSmooth π) (hρ : IsSmooth ρ)
    (hc : IsCompact (K : Set G)) {x : V} {y : W}
    (h : ∀ g, ∃ c : ℂ, idem hπ hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y) (a : MonoidAlgebra ℂ G) :
    ∃ c : ℂ, idem hπ hc (orbitMap π x a) = c • x ∧ idem hρ hc (orbitMap ρ y a) = c • y := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨c, ha, hb⟩ := h g
    refine ⟨c, ?_, ?_⟩
    · show idem hπ hc (π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x) = _
      simpa using ha
    · show idem hρ hc (ρ.asAlgebraHom (MonoidAlgebra.of ℂ G g) y) = _
      simpa using hb
  | add a b ha hb =>
    obtain ⟨c, h1, h2⟩ := ha
    obtain ⟨d, h3, h4⟩ := hb
    exact ⟨c + d, by rw [map_add (f := _), map_add (f := _), h1, h3, add_smul], by rw [map_add (f := _), map_add (f := _), h2, h4, add_smul]⟩
  | smul r a ha =>
    obtain ⟨c, h1, h2⟩ := ha
    exact ⟨r * c, by rw [map_smul, map_smul, h1, mul_smul], by rw [map_smul, map_smul, h2, mul_smul]⟩

theorem isSubquot_of_hecke_eigenvalues (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W)
    (K : Subgroup G) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K) (hπ : IsIrrSmooth π) (hρ : IsSmooth ρ)
    (x : V) (hx : x ∈ fixed π K) (hx0 : x ≠ 0) (y : W) (hy : y ∈ fixed ρ K) (hy0 : y ≠ 0)
    (h : ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) : IsSubquot π ρ := by
  have h1 : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y := fun g => by
    obtain ⟨c, ha, hb⟩ := h _ (Final.DosetIndMem G K ℂ g)
    rw [heckeVec_dosetInd hπ.1 hc hK hx] at ha
    rw [heckeVec_dosetInd hρ hc hK hy] at hb
    have hn := card_ne_zero hK g
    refine ⟨((P.finite_cosets_in_doset hK g).toFinset.card : ℂ)⁻¹ * c, ?_, ?_⟩
    · rw [mul_smul, ← ha, inv_smul_smul₀ hn]
    · rw [mul_smul, ← hb, inv_smul_smul₀ hn]
  let T : Subrepresentation π :=
    ⟨⨅ g, LinearMap.ker (idem hπ.1 hc ∘ₗ π g), fun g v hv => by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hv ⊢
      intro g'
      simpa using hv (g' * g)⟩
  have hT : T = ⊥ := by
    haveI := hπ.2
    refine (eq_bot_or_eq_top T).resolve_right fun e => hx0 ?_
    have : x ∈ T := e ▸ trivial
    have h2 : idem hπ.1 hc (π 1 x) = 0 := (Submodule.mem_iInf _).1 this 1
    rwa [map_one, Module.End.one_apply, idem_of_mem hπ.1 hc hx] at h2
  have hker : LinearMap.ker (orbitMap ρ y).toLinearMap ≤ LinearMap.ker (orbitMap π x).toLinearMap := fun a h0 => by
    have h0' : orbitMap ρ y a = 0 := h0
    have : orbitMap π x a ∈ T := (Submodule.mem_iInf _).2 fun g => by
      show idem hπ.1 hc (π g (orbitMap π x a)) = 0
      obtain ⟨c, h2, h3⟩ := idem_orbitMap hπ.1 hρ hc h1 (Representation.leftRegular ℂ G g a)
      rw [(orbitMap ρ y).isIntertwining, h0', map_zero, map_zero] at h3
      rw [← (orbitMap π x).isIntertwining, h2,
        (smul_eq_zero.1 h3.symm).resolve_right hy0, zero_smul]
    rw [hT] at this
    exact this
  let f : (orbitMap ρ y).range.toSubmodule →ₗ[ℂ] V :=
    Submodule.liftQ _ _ hker ∘ₗ (orbitMap ρ y).toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ a h, f ⟨orbitMap ρ y a, h⟩ = orbitMap π x a := fun a h => by
    have := (orbitMap ρ y).toLinearMap.quotKerEquivRange_symm_apply_image a h
    exact (congrArg (Submodule.liftQ _ _ hker) this).trans rfl
  refine ⟨(orbitMap ρ y).range, ⟨f, fun g => LinearMap.ext ?_⟩, fun v => ?_⟩
  · rintro ⟨_, a, rfl⟩
    have e := (orbitMap ρ y).isIntertwining _ _ g a
    have e' : (orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩ =
        ⟨orbitMap ρ y (Representation.leftRegular ℂ G g a), _, rfl⟩ := Subtype.ext e.symm
    show f ((orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩) = π g (f ⟨orbitMap ρ y a, a, rfl⟩)
    rw [e']
    exact (hf _ _).trans (((orbitMap π x).isIntertwining _ _ g a).trans (congrArg (π g) (hf _ _).symm))
  · obtain ⟨a, rfl⟩ := orbitMap_surjective hπ.2 hx0 v
    exact ⟨⟨_, a, rfl⟩, hf a _⟩

end GlobalTheory.LGrp.Zonal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaCube

theorem cube_addInt_beBiadd : ∀ D : D7, GL3Theta.cube D ∧ GL3Theta.addInt D ∧ GL3Theta.beBiadd D := by
  intro D
  have hc : GL3Theta.cube D := Formalism.MainNotions.Ext.CutA.theorem_of_cube_of_addition_formulas D (_root_.GlobalTheory.SigmaAdd.sigma_add_param D) (_root_.GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula D)
  exact ⟨hc, Formalism.MainNotions.Ext.addInt_holds D, Formalism.MainNotions.Ext.beBiadd_of_cube D hc⟩

end GlobalTheory.ThetaCube
end

