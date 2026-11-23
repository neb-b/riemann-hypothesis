module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSqNonsplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

open TensorProduct

namespace GlobalTheory.InertUmax

theorem tensor_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

theorem tensor_decomp_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add (f := _), TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at h0 h1
  exact ⟨h0, h1⟩

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

omit [IsCMField L] in
theorem compAt_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : L) (a : AFplus L) :
    compAt L v (x ⊗ₜ[maximalRealSubfield L] a) = x ⊗ₜ[maximalRealSubfield L] (a v) := by
  simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul]
  rfl

theorem eq_zero_of_compAt (z : AL L) (hz : ∀ v, compAt L v z = 0) : z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨A, B, hAB⟩ := tensor_decomp b z
  have hoff : ∀ w, A w = 0 ∧ B w = 0 := by
    intro w
    have h := hz w
    rw [hAB, map_add (f := _), compAt_tmul, compAt_tmul] at h
    exact tensor_decomp_zero b _ _ h
  have hA : A = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).1
  have hB : B = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).2
  rw [hAB, hA, hB]; simp


open Classical in
def sgl (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : AFplus L :=
  ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r, by
    refine Filter.mem_of_superset (Set.finite_singleton v).compl_mem_cofinite ?_
    intro w hw
    have hw' : w ≠ v := hw
    simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hw']
    exact zero_mem _⟩

omit [IsCMField L] in
theorem sgl_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : sgl L v r v = r := by
  classical
  exact Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r

omit [IsCMField L] in
theorem sgl_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) {w} (hw : w ≠ v) : sgl L v r w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) hw r

omit [IsCMField L] in
theorem one_tmul_sgl_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L))
    (hr : r ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v r : AL L) ∈ ALint L := by
  refine Subring.subset_closure (Or.inr ⟨sgl L v r, fun w => ?_, rfl⟩)
  rcases eq_or_ne w v with rfl | hw
  · rw [sgl_same]; exact hr
  · rw [sgl_ne L v r hw]; exact zero_mem _


omit [IsCMField L] in
theorem exists_lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hy : y ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    ∃ Y ∈ ALint L, compAt L v Y = y := by
  have key : tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ≤ (ALint L).map (compAt L v) := by
    rw [tensInt, Subring.closure_le]
    rintro _ (⟨⟨_, s, rfl⟩, rfl⟩ | ⟨r, rfl⟩)
    · refine ⟨(s : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L),
        Subring.subset_closure (Or.inl ⟨s, rfl⟩), ?_⟩
      rw [compAt_tmul]; rfl
    · refine ⟨_, one_tmul_sgl_mem L v r r.2, ?_⟩
      rw [compAt_tmul, sgl_same]
  exact key hy

theorem mem_ALint_of_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : AL L)
    (hoff : ∀ w, w ≠ v → compAt L w x = 0)
    (hv : compAt L v x ∈ tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    x ∈ ALint L := by
  obtain ⟨Y, hY, hYv⟩ := exists_lift L v _ hv
  have h : x - Y * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1) = 0 := by
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, compAt_tmul]
    rcases eq_or_ne w v with rfl | hw
    · rw [sgl_same, hYv, ← Algebra.TensorProduct.one_def, mul_one, sub_self]
    · rw [sgl_ne L v 1 hw, hoff w hw, tmul_zero, mul_zero, sub_self]
  rw [sub_eq_zero.1 h]
  exact Subring.mul_mem _ hY (one_tmul_sgl_mem L v 1 (one_mem _))

theorem entries_mem_of_range {K : Type} [Field K] (S : Subring K) {n : ℕ} (P : GL (Fin n) K)
    (hP : P ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range) (i j : Fin n) :
    (P : Matrix (Fin n) (Fin n) K) i j ∈ S := by
  obtain ⟨Q, rfl⟩ := hP
  exact ((Q : Matrix (Fin n) (Fin n) S) i j).2

theorem mem_Umax_of_trivOutside_of_loc_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (z : GAf L n), TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n := by
  intro L _ _ _ n v w Dv z hz hint i j
  have hP := entries_mem_of_range _ _ Dv.Pint
  have hP' := entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hg : Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (z : GL (Fin n) (AL L))) =
      Dv.P * Dv.loc z * Dv.P⁻¹ := by
    unfold InertDatum.loc
    group
  have he : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) ∈
      intL (w.adicCompletion L) := by
    have h1 : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) =
        ((Dv.P * Dv.loc z * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j := by
      rw [← hg]; rfl
    rw [h1]
    simp only [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
      (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP i l) (hint l k)) (hP' k j)
  have hv := (Dv.integ _).2 he
  have hone : ∀ {R : Type} [CommRing R] (S : Subring R), (1 : Matrix (Fin n) (Fin n) R) i j ∈ S := by
    intro R _ S
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hc : ∀ u, compAt L u ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro u
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hd : (z.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈
      ALint L := by
    apply mem_ALint_of_supported L v
    · intro u hu
      have h := congrFun (congrFun (hz u hu) i) j
      rw [map_sub, hc, ← h, Matrix.map_apply, sub_self]
    · rw [map_sub, hc]
      exact Subring.sub_mem _ hv (hone _)
  have := Subring.add_mem _ hd (hone (ALint L))
  rwa [sub_add_cancel] at this

end GlobalTheory.InertUmax
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySpec
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC

noncomputable section

namespace GlobalTheory.HeckeLocN

set_option synthInstance.maxHeartbeats 400000

section Transport

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {B : LocBase0 H what₂} {i : LocT B} {j : ℕ} {w : what₂.places.Pl}
  (h : jOf B i = j ∧ wOf B i = w)

def trO : OOf B i ≃+* B.Oc j w := by obtain ⟨rfl, rfl⟩ := h; exact RingEquiv.refl _

def trK : FractionRing (OOf B i) ≃+* FractionRing (B.Oc j w) := by obtain ⟨rfl, rfl⟩ := h; exact RingEquiv.refl _

theorem trK_alg (z : OOf B i) : trK h (algebraMap _ _ z) = algebraMap _ _ (trO h z) := by obtain ⟨rfl, rfl⟩ := h; rfl

theorem trK_ec (x : what₂.LL) : trK h (B.ec _ _ x) = B.ec j w x := by obtain ⟨rfl, rfl⟩ := h; rfl

variable (hC : PartCompl B) (hL : MtLoc B hC)

def trPsi : TensorProduct (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) →ₛₗ[(trK h).toRingHom] B.V j w := by
  obtain ⟨rfl, rfl⟩ := h
  exact { toFun := PsiC B hC hL i, map_add' := map_add _, map_smul' := fun c z => map_smul (PsiC B hC hL i) c z }

theorem trPsi_inj : Function.Injective (trPsi h hC hL) := by obtain ⟨rfl, rfl⟩ := h; exact PsiC_inj B hC hL i

theorem trPsi_range (y : B.V j w) : y ∈ NCov.part (heckeAlg0 B j w) (mxC B j w i) ↔ ∃ z, trPsi h hC hL z = y := by
  obtain ⟨rfl, rfl⟩ := h
  rw [mxC_self]
  exact PsiC_range B hC hL i y

theorem trPsi_pr (x : what₂.MtL (what₂.muTw (wOf B i)) (jOf B i)) (x' : what₂.MtL (what₂.muTw w) j) (hx : HEq x' x) :
    trPsi h hC hL (prMtC B hC hL i x) - B.iV j w x' ∈ NCov.off (heckeAlg0 B j w) (mxC B j w i) := by
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl := eq_of_heq hx
  rw [mxC_self]
  exact PsiC_pr B hC hL i _

def trX : XOf B i ≃ {ψ : heckeAlg0 B j w →ₐ[B.Oc j w] B.Oc j w //
    NCov.cls ψ = mxC B j w i ∧ NCov.W (heckeAlg0 B j w) (NCov.pt ψ) ≠ ⊥} := by
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨fun x => ⟨x.1, x.2.1.trans (mxC_self B i).symm, x.2.2⟩, fun x => ⟨x.1, x.2.1.trans (mxC_self B i), x.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem trX_hT (x : XOf B i) (v : PlE H) (k : ℕ) (hvk : GenAt0 H (what₂.places.resChar w) (B.Qw w) v k) :
    trO h ((hTOf B i v k : XOf B i → OOf B i) x) = (trX h x).1 ⟨B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
  obtain ⟨rfl, rfl⟩ := h
  exact ptX_val B i v k hvk x

theorem trPsi_act (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd))
    (hA : ActHK B hs hd hL hAct) (v : PlE H) (k : ℕ) (hvk : GenAt0 H (what₂.places.resChar w) (B.Qw w) v k) (z) :
    trPsi h _ hL (((actC B (partCompl_of hs hd) hAct i) (hTOf B i v k)).baseChange (FractionRing (OOf B i)) z) =
      B.hK j w v k (trPsi h _ hL z) := by
  obtain ⟨rfl, rfl⟩ := h
  exact hA i v k hvk z

include h in
theorem tr_max : (mxC B j w i).IsMaximal := by obtain ⟨rfl, rfl⟩ := h; exact mxC_max B i

end Transport

variable {D : D7}

def recBase (M : MtFam D) (B0 : LocBase0 D.host D.what₂)
    (hdef : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (B0.Qw w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (B0.hL j w v k x)) =
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)))
    (hO : ∀ w (v v' : PlE D.host), v ∈ B0.Qw w →
      (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ B0.Qw w)
    (hc : ∀ w (v v' : PlE D.host), v' ∈ B0.Qw w → IsConjPl D.host v v' → v ∈ B0.Qw w) : NLocBase D M where
  Oc := B0.Oc
  ec := B0.ec
  ec_w := B0.ec_w
  V := B0.V
  iV := B0.iV
  iV_basis := B0.iV_basis
  Qc _ w := B0.Qw w
  hL := B0.hL
  hL_def := hdef
  hK := B0.hK
  hK_def := B0.hK_def
  split := B0.split
  Qc_over _ := hO
  Qc_conj _ := hc

section Spec

variable (B0 : LocBase0 D.host D.what₂) (C : NChoice D) (hs : HeckeStd0 B0) (hd : FinDimV B0)
  (hL : MtLoc B0 (partCompl_of hs hd))
  (hMF : ∀ i, Module.Free (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hMFin : ∀ i, Module.Finite (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hTL : ∀ i, IsLocalRing (TOf B0 i)) (hAct : ActEx B0 (partCompl_of hs hd))
  (hEig : ∀ i x, heckeEig (TOf B0 i) (actC B0 (partCompl_of hs hd) hAct i) x ≠ ⊥)
  (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
  (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ)
  (hChi : ∀ i c, Continuous (fun g => ((chiN B0 C tw ps i c g : (OOf B0 i)ˣ) : OOf B0 i)))
  (hSQs : ∀ i v, v ∈ (exceptional_places_finite D.host (lOf B0 i)).toFinset ∨ v ∈ B0.Qw (wOf B0 i) → IsSplitPl D.host v)
  (hSQd : ∀ i, Disjoint (exceptional_places_finite D.host (lOf B0 i)).toFinset (B0.Qw (wOf B0 i)))
  (hQl : ∀ w v, v ∈ B0.Qw w → v ∉ placesOver D.host.E (D.what₂.places.resChar w))
  (hRam : ∀ i, ∀ v ∈ B0.Qw (wOf B0 i), ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chi1N B0 C tw ps i g ≠ 1)
  (hI : OsInt B0) (hBF : ∀ i, Module.Free (OOf B0 i) (BjC B0 hI i))

attribute [local instance] LocBase0.algOc


set_option maxHeartbeats 1000000 in
theorem nonempty_spec
    (hTwE : ∀ (a : LocT B0) (x : D.LL0) (y : D.ntw.O0 (C.twI (wOf B0 a))),
      algebraMap (D.ntw.O0 (C.twI (wOf B0 a))) (FractionRing (D.ntw.O0 (C.twI (wOf B0 a)))) y =
        (if C.sd (wOf B0 a) then D.ntw.emb0 (C.twI (wOf B0 a)) else D.ntw.emb0b (C.twI (wOf B0 a))) x →
      B0.ec (jOf B0 a) (wOf B0 a) (x : D.what₂.LL) = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y))
    (hOrd : ∀ a g, ∃ n : ℕ, ps a g ^ (lOf B0 a ^ n) = 1)
    (hOpen : ∀ a, IsOpen ((ps a).ker : Set (G D.host.E D.nd.Om)))
    (hAnti : ∀ a, AntiHom D.ntw.cc (ps a))
    (hRamP : ∀ a, RamExactly (ps a) (↑(B0.Qw (wOf B0 a)) : Set (HeightOneSpectrum (𝓞 D.host.E))))
    (hPl : ∀ a v, v ∈ placesOver D.host.E (lOf B0 a) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ ∈ Dec (F := D.host.E) A, ps a σ = 1)
    (pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ)
    (hdef : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (B0.Qw w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (B0.hL j w v k x)) =
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)))
    (hO : ∀ w (v v' : PlE D.host), v ∈ B0.Qw w →
      (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ B0.Qw w)
    (hc : ∀ w (v v' : PlE D.host), v' ∈ B0.Qw w → IsConjPl D.host v v' → v ∈ B0.Qw w)
    (hQ : ∀ w, B0.Qw w = C.Q w)
    (iq : ∀ j w, FractionRing (B0.Oc j w) →+* Qbar (D.what₂.places.resChar w))
    (hiA : ∀ j w (z : ℤ_[D.what₂.places.resChar w]), iq j w (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w))
      (algebraMap ℤ_[D.what₂.places.resChar w] (B0.Oc j w) z)) =
        algebraMap ℚ_[D.what₂.places.resChar w] (Qbar (D.what₂.places.resChar w)) (z : ℚ_[D.what₂.places.resChar w]))
    (hiL : ∀ j w x, pl.ι w (iq j w (B0.ec j w x)) = D.what₂.embLL x)
    (hBig : ∀ j w, ∀ z ∈ big w, ∃ x, pl.ι w (iq j w x) = z)
    (hAHK : ActHK B0 hs hd hL hAct) (hD : PlGwDisj D)
    (hψ : ∀ (a : LocT B0) (g : G D.host.E D.nd.Om) (y : D.what₂.LL), C.embW (wOf B0 a) y =
      algebraMap (C.Oe (wOf B0 a)) (FractionRing (C.Oe (wOf B0 a)))
        (algebraMap (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a))) (C.Oe (wOf B0 a))
          ((C.psi' (wOf B0 a) (D.ntw.art (C.twI (wOf B0 a)) (C.Q (wOf B0 a)) g) :
            (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a)))ˣ) : D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a)))) →
      B0.ec _ _ y = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) ((ps a g : (OOf B0 a)ˣ) : OOf B0 a))
    (hTwA : ∀ a : LocT B0, haveI : Fact (D.ntw.l (C.twI (wOf B0 a))).Prime := D.ntw.lPrime (C.twI (wOf B0 a))
      ∀ (z : ℤ_[D.ntw.l (C.twI (wOf B0 a))]) (z' : ℤ_[D.what₂.places.resChar (wOf B0 a)]), HEq z z' →
      tw a (@algebraMap _ (D.ntw.O0 (C.twI (wOf B0 a))) _ _ (D.ntw.algO0 (C.twI (wOf B0 a))) z) = algebraMap _ (OOf B0 a) z')
    (hTwR : ∀ a : LocT B0, ∃ (Ω : Type) (_ : Field Ω) (τ : FractionRing (OOf B0 a) →+* Ω)
      (ι : FractionRing (C.Oe (wOf B0 a)) →+* Ω),
      (∀ y, τ (algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y)) =
        ι (algebraMap (C.Oe (wOf B0 a)) (FractionRing (C.Oe (wOf B0 a)))
          (algebraMap (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a))) (C.Oe (wOf B0 a))
            (BlochKatoReduction.Gen.phiK D.ntw (C.twI (wOf B0 a)) (C.k' (wOf B0 a)) y)))) ∧
      ∀ x : D.what₂.LL, τ (B0.ec _ _ x) = ι (C.embW (wOf B0 a) x))
    (hBr : ∀ j w (u : PlE D.host), u ∈ placesOver D.host.E (D.what₂.places.resChar w) →
      ∃ Bw : LocBridge (D.what₂.places.resChar w) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 u)) (B0.Oc j w),
        (∀ x, x ∈ D.nd.plOm.1 u ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef D.host.condN Bw.LL ∧
        ∀ z : B0.Oc j w, iq j w (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w)) z) =
          ((Bw.toLL z : ↥Bw.LL.1) : Loc.Om (D.what₂.places.resChar w))) :
    Nonempty (NdSpec pl M C big (mkX B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF) (mkT B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF hTwE hOrd hOpen hAnti hRamP hPl)) := ⟨{
  iq i := iq (jOf B0 i) (wOf B0 i)
  iq_alg i := hiA _ _
  iq_LL i := hiL _ _
  iq_big i := hBig _ _
  B := recBase M B0 hdef hO hc
  Q_eq j w i h := congrArg B0.Qw ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h).2
  mx := mxC B0
  mx_max j w i h := tr_max ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  mx_inj := mxC_inj B0 (locsFin_of hs hd)
  mx_all := mxC_all B0 (locsFin_of hs hd)
  phO j w i h := trO ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK j w i h := trK ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK_alg j w i h := trK_alg ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK_emb j w i h := trK_ec ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  Psi j w i h := trPsi ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_inj j w i h := trPsi_inj ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_range j w i h := trPsi_range ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_pr j w i h x := trPsi_pr ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL x _ (cast_heq _ _)
  ptX j w i h := trX ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  ptX_hT j w i h := trX_hT ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  iotaC j w := (pl.ι w).toRingHom.comp ((iq j w).comp (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w))))
  iotaC_coh j w i h z := by
    obtain ⟨rfl, rfl⟩ := ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
    rfl
  Qc_eq _ := hQ
  std := hs
  act_hK j w i h := trPsi_act ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) hs hd hL hAct hAHK
  twOf_eq _ := rfl
  twSide_eq _ := rfl
  psi_eq := hψ
  twO_alg := hTwA
  tw_reads a := ⟨tw a, HEq.rfl, hTwR a⟩
  heckeLoc_gamma_places _ := gamN_tg D hD
  nbr i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose
  nbr_ind i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.1
  self_good i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.2.1
  nbr_iq i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.2.2
  bj := bjC B0 hI
  bj_span := bjC_span B0 hI
  bj_rel i s hs' c := by
    obtain rfl : s = sOfC B0 hI i := RingHom.ext fun y => IsFractionRing.injective (OOf B0 i) (FractionRing (OOf B0 i))
      ((hs' y).trans (congrArg Subtype.val ((fracRangeEquiv (OOf B0 i)).apply_symm_apply ⟨_, hI _ _ y⟩)).symm)
    exact bjC_rel B0 hI i c }⟩

end Spec

end GlobalTheory.HeckeLocN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitTw

variable {D : D7}


set_option maxHeartbeats 2000000 in
def twFL (L : LocAll (lay0 D)) (F : TwFrameC D) : TwFrameC (withLoc L) := { F with }

set_option maxHeartbeats 4000000 in
theorem twTiedL (L : LocAll (lay0 D)) {F : TwFrameC D} {low : Finset ℕ} (h : TwistFrameLowIndexCompatibility D F low) :
    TwistFrameLowIndexCompatibility (withLoc L) (twFL L F) low := { h with }

set_option maxHeartbeats 4000000 in
theorem choiceL (L : LocAll (lay0 D)) {C : NChoice D} (h : ChoiceC D C) : ChoiceC (withLoc L) (chL L C) := { h with }


set_option maxHeartbeats 20000000 in
def mtVL (L : LocAll (lay0 D)) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [g : AddCommGroup W₀]
    [m : Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (V : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) : @NX.MtVReal (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ :=
  @NX.MtVReal.mk (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ V.W V.acg V.mod V.fd V.ρ V.irr V.alg V.bc V.J V.χ V.J_open V.hyp V.QP V.QP_sub V.QP_cover V.QP_nconj V.DP V.DP_sub V.DP_cover V.DP_nconj V.sp V.sp_w V.redG V.J_mem V.chi_eq V.real


set_option maxHeartbeats 4000000 in
def expL (L : LocAll (lay0 D)) (X : NExpTied D) : NExpTied (withLoc L) :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      (@mtVL D L i j b k Q ψ X.sgnT (X.Wt i j b) (X.acgWt i j b) (X.modWt i j b) (X.rhoW i j b) (X.tauG i j b) (X.mtV i j b k Q ψ h1 h2 h)) }

set_option maxHeartbeats 4000000 in
theorem nctL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) (h : NChTie D C) : NChTie (withLoc L) (chL L C) := by
  obtain ⟨ψ0, h1, h2, -⟩ := h.psi_eq
  exact {
    twOf_eq := Sp.twOf_eq
    twSide_eq := Sp.twSide_eq
    Q_eq a := (Sp.Q_eq _ _ a ((L.X.locs_mem _ _ a).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
    psi_eq := ⟨ψ0, h1, h2, fun a g => Sp.psi_eq a g _ (h2 _ g)⟩
    embedding_baseField_condition := h.embedding_baseField_condition }

set_option maxHeartbeats 4000000 in
theorem chSideL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) {cf : CharFrame D} {X : NExpTied D} {tp : TupTied D cf C}
    (h : ChoiceSide D cf M X C tp) : ChoiceSide (withLoc L) (cfL L cf) (mtL L M) (expL L X) (chL L C) (tpL L tp) := by
  exact {
    nct := nctL Sp h.nct
    choice := choiceL L h.choice
    off := h.off
    adm := h.adm
    psi := h.psi
    eMt_level := h.eMt_level }



set_option maxHeartbeats 4000000 in
def chiDL (L : LocAll (lay0 D)) (K : NC.NChiData D) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E) : NC.NChiData (withLoc L) :=
  { K with psi := ψ }

set_option maxHeartbeats 4000000 in
theorem chiL (L : LocAll (lay0 D)) {K : NC.NChiData D} (h : NC.NormalizedCharacterCompatibility D K) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) :
    NC.NormalizedCharacterCompatibility (withLoc L) (chiDL L K ψ) :=
  { h with psi := hψ }

set_option maxHeartbeats 4000000 in
theorem deltaReadL (L : LocAll (lay0 D)) {cf : CharFrame D} (h : DeltaRead D cf) : DeltaRead (withLoc L) (cfL L cf) := h


end GlobalTheory.HeightCounting.FitTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjectiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_kummer_inertia_surjective : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y := by
  first | exact @GlobalTheory.TameKummerInertia.tame_kummer_surj | exact GlobalTheory.TameKummerInertia.tame_kummer_surj | (intros; apply GlobalTheory.TameKummerInertia.tame_kummer_surj <;> assumption)
end

