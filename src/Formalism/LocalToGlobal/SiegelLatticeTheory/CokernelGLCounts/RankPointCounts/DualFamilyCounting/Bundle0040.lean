module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingDataFurther
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0076
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetUnitOfSelfdual
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
  Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem det_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) :
    G.det ∈ SP K 𝔭 := by
  have e : G.det = (SP K 𝔭).subtype
      (Matrix.det (Matrix.of fun i j => (⟨G i j, hG i j⟩ : SP K 𝔭))) := by
    rw [RingHom.map_det]; rfl
  rw [e]
  exact SetLike.coe_mem _

theorem gram_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) (β : Basis κ K V) :
    (gramK h β).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hy : ∀ x, h x (β.equivFun.symm v) = 0 := by
    intro x
    rw [form_repr h β, LinearEquiv.apply_symm_apply, hGv]
    simp
  have h0 : β.equivFun.symm v = 0 := by
    apply hnd
    intro y
    have := hs.eq y (β.equivFun.symm v)
    rw [← this, hy y, map_zero]
  exact β.equivFun.symm.injective (by rw [h0, map_zero])

private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) K) (x : K) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma star_fix_lemma_2 (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, -, rfl⟩ := hx
    exact (hF _).mpr ⟨(t : F), rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, star_mul', hx, hy]

private lemma star_mem_SP' (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K}
    (ha : a ∈ SP K 𝔭) : star a ∈ SP K 𝔭 := by
  rw [mem_SP_iff_locF] at ha ⊢
  obtain ⟨s, hs', hsa⟩ := (mem_locF_lemma 𝔭 _ a).mp ha
  obtain ⟨z, hz⟩ := Submodule.mem_one.mp hsa
  obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range z
  refine (mem_locF_lemma 𝔭 _ _).mpr ⟨s, hs', Submodule.mem_one.mpr ⟨r, ?_⟩⟩
  rw [hr, hz, Algebra.smul_def, Algebra.smul_def, star_mul', star_fix_lemma_2 hF hs']

theorem det_unit_of_selfdual (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) (β : Basis κ K V) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]
    (hsd : dualF h 𝔭 (locF 𝔭 (spanO β)) = locF 𝔭 (spanO β)) :
    (gramK h β).det ∈ SP K 𝔭 ∧ (gramK h β).det⁻¹ ∈ SP K 𝔭 := by
  have hdet := gram_det_ne_zero hs hnd β
  have hunit : IsUnit (gramK h β).det := isUnit_iff_ne_zero.mpr hdet
  have hmemL : ∀ x, x ∈ locF 𝔭 (spanO β) ↔ ∀ i, β.equivFun x i ∈ SP K 𝔭 :=
    fun x => mem_locF_iff_repr β x
  have hβ : ∀ i, β i ∈ locF 𝔭 (spanO β) := fun i => by
    simpa using smul_basis_mem β (SP K 𝔭).one_mem i
  have hdual : ∀ x ∈ locF 𝔭 (spanO β), ∀ y ∈ locF 𝔭 (spanO β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hsd] at hx
    exact hx
  have hG : Ent (SP K 𝔭) (gramK h β) := fun i j =>
    mem_SP_iff_locF.mpr (hdual _ (hβ j) _ (hβ i))
  have hinv : gramK h β * (gramK h β)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hcol : ∀ k l, (gramK h β)⁻¹ l k ∈ SP K 𝔭 := by
    intro k l
    obtain ⟨x, hxdef⟩ : ∃ x : V, β.equivFun x = (gramK h β)⁻¹ *ᵥ Pi.single k (1 : K) :=
      ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    have hx : x ∈ locF 𝔭 (spanO β) := by
      rw [← hsd]
      change ∀ y ∈ locF 𝔭 (spanO β), h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
      intro y hy
      rw [← mem_SP_iff_locF, form_repr h β, hxdef, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      convert star_mem_SP' hF ((hmemL y).mp hy k) using 1
      simp [dotProduct, Pi.single_apply]
    have hc := (hmemL x).mp hx l
    rw [hxdef] at hc
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hc
  have hdi : ((gramK h β)⁻¹).det = (gramK h β).det⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨det_mem_SP hG, ?_⟩
  rw [← hdi]
  exact det_mem_SP fun l k => hcol k l

theorem gram_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    gramK h γ = (β.toMatrix γ)ᴴ * gramK h β * β.toMatrix γ := by
  ext i j
  have e : gramK h γ i j = h (γ i) (γ j) := rfl
  rw [e, form_repr h β, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Basis.toMatrix_apply, Basis.equivFun_apply, Pi.star_apply]

theorem gram_det_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    (gramK h γ).det = star (β.toMatrix γ).det * (gramK h β).det * (β.toMatrix γ).det := by
  rw [gram_change h β γ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]

theorem gram_det_orth (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : Basis κ K V)
    (ho : ∀ s t, s ≠ t → h (γ s) (γ t) = 0) : (gramK h γ).det = ∏ s, h (γ s) (γ s) := by
  have e : gramK h γ = Matrix.diagonal fun s => h (γ s) (γ s) := by
    ext s t
    by_cases hst : s = t
    · subst hst; simp [gramK]
    · simp [gramK, Matrix.diagonal_apply_ne _ hst, ho s t hst]
  rw [e, Matrix.det_diagonal]

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingData
section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

def liftQ {K F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    (M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : Matrix (Fin m) (Fin m) (𝓞 K) :=
  Matrix.of fun i j => (Ideal.Quotient.mk_surjective (M i j)).choose

theorem liftQ_map {K F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    (M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (liftQ M).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = M := by
  ext i j
  simp only [Matrix.map_apply, liftQ, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (M i j)).choose_spec

end Formalism.L2.SG.Pf.fibreCountingData

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G5 Formalism.L2.SG.Pf.discriminantNormShapes Formalism.L2.SG.Pf.fibreCountingData

theorem unitary_discriminant_model : UDModel := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hK h hs hd L hL hLi 𝔭 h𝔭 b a hb k hk
  have hli := linearIndependent_of_jordan hb
  have hcard : Fintype.card (Fin (finrank K (⊤ : Submodule K V))) = finrank K V := by
    simp [finrank_top]
  have hbspan := hli.span_eq_top_of_card_eq_finrank' hcard
  obtain ⟨-, hloc, horth, hdiag, hne⟩ := hb
  have hfull : Submodule.span K (L : Set V) = ⊤ := by
    apply top_unique
    rw [← hbspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : b i ∈ locF 𝔭 L := by
      rw [← hloc]
      exact Formalism.HermitianLattices.Ext.L3.localizedQuotients.le_locF 𝔭 _
        (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hmem
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      clear hsx
      induction hs using Submonoid.closure_induction with
      | mem y hy =>
        obtain ⟨t, ht, rfl⟩ := hy
        rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
          IsScalarTower.algebraMap_apply (𝓞 F) F K]
        exact (map_ne_zero (algebraMap F K)).2
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (fun ht0 => ht (ht0 ▸ 𝔭.zero_mem)))
      | one => simp
      | mul x y _ _ hx hy => simp only [map_mul]; exact mul_ne_zero hx hy
    have hsx' : algebraMap (𝓞 K) K s • b i ∈ Submodule.span K (L : Set V) := by
      rw [algebraMap_smul]; exact Submodule.subset_span hsx
    exact (Submodule.smul_mem_iff _ hs0).1 hsx'
  have hFx : IsFixF K F := Fact.out
  let s := udSetoid K 𝔭 k a
  let J : JD h L 𝔭 b a := ⟨horth, hdiag, hne, hloc, hFx, h𝔭, ⟨hL.fg, hfull⟩⟩
  have := h𝔭.isPrime
  have hv : ∀ i, vF 𝔭 (a i) ≤ vJof 𝔭 a := fun i =>
    Finset.single_le_sum (f := fun i => vF 𝔭 (a i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hk1 : ∀ i, vF 𝔭 (a i) ≤ k := fun i => by have := hv i; omega
  have hk2 : ∀ i j, vF 𝔭 (a i) + vF 𝔭 (a j) ≤ k := fun i j => by
    have := hv i; have := hv j; omega
  have hA : ∀ Y : udPre K 𝔭 k a, ∀ i j,
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i) * liftQ Y.1 i j) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ HU.SP K 𝔭 := fun Y =>
    (condP_iff_eqP hne hk1 (liftQ Y.1)).1 (by rw [liftQ_map]; exact Y.2.1)
  have hW : ∀ Y : udPre K 𝔭 k a, ∀ i j,
      algebraMap (𝓞 K) K (gramO a (liftQ Y.1) i j) / (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) ∈ HU.SP K 𝔭 := fun Y =>
    (condW_iff hne hk2 (liftQ Y.1)).1 (by rw [liftQ_map]; exact Y.2.2)
  let f0 : udPre K 𝔭 k a → {P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) //
      ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
        Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
        Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
        h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)} :=
    fun Y => ⟨J.E (liftQ Y.1) (hA Y), J.E_isom (liftQ Y.1) (hA Y) (hW Y)⟩
  have hresp : ∀ Y Y' : udPre K 𝔭 k a, s.r Y Y' → f0 Y = f0 Y' := by
    rintro Y Y' ⟨Z, hZ⟩
    have hd := (condZ_iff hne hk1 (liftQ Y.1) (liftQ Y'.1)).mp
      ⟨Z, by simpa only [liftQ_map] using hZ⟩
    exact Subtype.ext (J.E_eq_of (liftQ Y.1) (liftQ Y'.1) (hA Y) (hA Y') hd)
  let f : udQ K 𝔭 k a → _ := Quotient.lift (s := s) f0 hresp
  have hinj : Function.Injective f := by
    intro q q'
    induction q using Quotient.inductionOn with | h Y => ?_
    induction q' using Quotient.inductionOn with | h Y' => ?_
    intro he
    have he' : J.E (liftQ Y.1) (hA Y) = J.E (liftQ Y'.1) (hA Y') := congrArg Subtype.val he
    apply Quotient.sound
    obtain ⟨Z, hZ⟩ := (condZ_iff hne hk1 (liftQ Y.1) (liftQ Y'.1)).2
      (J.entry_of_E_eq (liftQ Y.1) (liftQ Y'.1) (hA Y) (hA Y') he')
    rw [liftQ_map, liftQ_map] at hZ
    exact ⟨Z, hZ⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨P, hP⟩
    have hLift := J.exists_E_eq P hP
    rcases hLift with ⟨Y, hY, hWY, hE⟩
    let Yq : udPre K 𝔭 k a :=
      ⟨Y.map (Ideal.Quotient.mk _), (condP_iff_eqP hne hk1 Y).2 hY, (condW_iff hne hk2 Y).2 hWY⟩
    refine ⟨Quotient.mk _ Yq, Subtype.ext ?_⟩
    refine (J.E_eq_of (liftQ Yq.1) Y (hA Yq) hY fun i j => ?_).trans hE
    have e := congrFun (congrFun (liftQ_map (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))) i) j
    rw [map_apply, map_apply, Ideal.Quotient.eq] at e
    exact div_mem_SP_of_mem h𝔭 (hne j) (hk1 j) e
  rw [discAut]
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLast
section
namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_of_last (hL : Formalism.L2.SG.Pf.GluingBases.LastUnit) : GlueExists :=
  glueExists_of_last_dual hL Formalism.L2.SG.Pf.GluingBases.family_dual_holds

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

abbrev BV : Type := ∀ q : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k q

def iQ (D : D7) (b a : Fin D.R.rS) : Set D.host.E :=
  ((aaD D b * (aaD D a)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)

def iP (D : D7) (b a : Fin D.R.rS) : Set D.host.E :=
  ((aaD D b * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)

def pW (y : (VS D).V) : (VS D).V :=
  y - ∑ c, (VS D).hT (X.fY c) y • X.eX c - ∑ c, (VS D).hT (X.eX c) y • X.fY c

def InW (y : (VS D).V) : Prop := ∀ c, (VS D).hT (X.eX c) y = 0 ∧ (VS D).hT (X.fY c) y = 0

def Xq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b a => (VS D).hT (X.fY b) (n (X.eX a))

def Aq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b a => (VS D).hT (X.fY b) (n (X.fY a))

def Mq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  (Xq X n)⁻¹ * Aq X n

def xq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : Fin D.R.rS) : (VS D).V := pW X (n.symm (X.fY b))

def Gq (D : D7) (xs : Fin D.R.rS → (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b c => (VS D).hT (xs b) (xs c)

def Gp (D : D7) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  X0⁻¹ * Gq D xs * (X0⁻¹)ᴴ

def DataOK (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : Prop :=
  (∀ b a : Fin D.R.rS, a < b → X0 b a = 0) ∧ (∀ a, X0 a a = 1) ∧ (∀ b, InW X (xs b)) ∧ M + Mᴴ = -Gp D X0 xs

def LatQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : Prop :=
  (∀ b a : Fin D.R.rS, b < a → X0 b a ∈ iQ D b a) ∧ (∀ b, xs b ∈ aaLb X b) ∧ ∀ b a, M b a ∈ iP D b a

variable (u : D.what₂.Word)

def NFl (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
    (∀ j, ∀ x ∈ Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Xflag (lf D (X.Fu u)) j) ∧
    ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), n x - x ∈ Xsp (lf D (X.Fu u))

def blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) :
    ∀ p : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl p) => embV X (X0 p.1.1 p.1.2)
  | Sum.inl (Sum.inr b) => rowV X u (xs b)
  | Sum.inr (Sum.inl p) => fun v =>
      (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2
  | Sum.inr (Sum.inr a) => fun v => (embS D (X.pl v) (M a a)).im


open scoped Classical in
def theta (D : D7) : D.host.E :=
  if h : ∃ t : D.host.E, IsIntegral ℤ t ∧ t + D.host.conj t = 1 then h.choose else 0

def Xc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b a => if h : b < a then x (Sum.inl (Sum.inl ⟨(b, a), h⟩)) v else if b = a then 1 else 0

def Gc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b c => (∑ j : Fin D.R.k, x (Sum.inl (Sum.inr b)) v (Fin.castSucc j) *
      star (x (Sum.inl (Sum.inr c)) v (Fin.castSucc j))) -
    x (Sum.inl (Sum.inr b)) v (Fin.last D.R.k) * star (x (Sum.inl (Sum.inr c)) v (Fin.last D.R.k)) /
      (((D.mem u).A.T : ℕ) : ℂ)

def Hc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  (Xc X x v)⁻¹ * Gc X u x v * ((Xc X x v)⁻¹)ᴴ

def tauQ : ∀ p : CBlk D.R.rS, BV X → CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl _) => fun _ => 0
  | Sum.inl (Sum.inr _) => fun _ => 0
  | Sum.inr (Sum.inl p) => fun x v => Hc X u x v p.1.1 p.1.2 / 2
  | Sum.inr (Sum.inr a) => fun x v => -((Hc X u x v a a).re * (embS D (X.pl v) (theta D)).im)

end Defs

def NOratC : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf),
    s ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔
      ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ x.1 = s ∧
        n ∈ NLam (VS D).L0 (lf D (X.Fu u))

def DictGram : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → DataOK X (Xq X n) (xq X n) (Mq X n)

def DictLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → (Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0 ↔ LatQ X (Xq X n) (xq X n) (Mq X n))

def DictEx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M →
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, NFl X u n ∧ Xq X n = X0 ∧ xq X n = xs ∧ Mq X n = M

def DictPlace : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    RatLink X x n → NFl X u n → blk X u x.1 = blkQ X u (Xq X n) (xq X n) (Mq X n)

def FibQ : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M →
    ((∀ p, blkQ X u X0 xs M p - tauQ X u p (blkQ X u X0 xs M) ∈ cLat X u p) ↔ LatQ X X0 xs M)

def FibOnto : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : BV X),
    (∀ p, x p - tauQ X u p x ∈ cLat X u p) →
      ∃ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
        (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M ∧ blkQ X u X0 xs M = x

def ThetaEx : Prop :=
  ∀ D : D7, ∃ t : D.host.E, IsIntegral ℤ t ∧ t + D.host.conj t = 1

theorem tauQ_lower {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : CBlk D.R.rS)
    (x x' : BV X) (h : ∀ q, cHgt q < cHgt p → x q = x' q) :
    tauQ X u p x = tauQ X u p x' := by
  rcases p with (p | b) | (p | a)
  · rfl
  · rfl
  all_goals
    have hX : ∀ q, x (Sum.inl q) = x' (Sum.inl q) := by
      intro q
      apply h
      rcases q with q | c
      · have := q.1.2.isLt
        simp only [cHgt]
        omega
      · have := c.isLt
        simp only [cHgt]
        omega
    have hH : Hc X u x = Hc X u x' := by
      funext v
      have hXc : Xc X x v = Xc X x' v := by
        funext i j
        simp only [Xc, hX]
      have hGc : Gc X u x v = Gc X u x' v := by
        funext i j
        simp only [Gc, hX]
      simp only [Hc, hXc, hGc]
    simp only [tauQ]
    rw [hH]

theorem nofibLat_of (hR : NOratC) (hG : DictGram) (hL : DictLat) (hE : DictEx) (hP : DictPlace) (hF : FibQ)
    (hO : FibOnto) : NOfibLat := by
  intro D X u
  refine ⟨tauQ X u, fun p x x' h => tauQ_lower X u p x x' h, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨xA, n, hlink, hx1, hn⟩ := (hR X u s).1 hs
    have hNF : NFl X u n := ⟨hn.1.1, hn.2.1, hn.2.2⟩
    have hD := hG X u n hNF
    have hLat := (hL X u n hNF).1 hn.1.2
    rw [← hx1, hP X u xA n hlink hNF]
    exact (hF X u _ _ _ hD).2 hLat
  · intro hx
    obtain ⟨X0, xs, M, hD, rfl⟩ := hO X u x hx
    have hLat := (hF X u X0 xs M hD).1 hx
    obtain ⟨n, hNF, h1, h2, h3⟩ := hE X u X0 xs M hD
    subst h1 h2 h3
    have hgm := (hL X u n hNF).2 hLat
    have hn : n ∈ NLam (VS D).L0 (lf D (X.Fu u)) := ⟨⟨hNF.1, hgm⟩, hNF.2.1, hNF.2.2⟩
    obtain ⟨xA, hlink⟩ := ratPt_holds D X n hNF.1
    exact ⟨xA.1, (hR X u xA.1).2 ⟨xA, n, hlink, rfl, hn⟩, hP X u xA n hlink hNF⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthogonalProjections
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.OrthogonalProjections

theorem fibre_counting_holds : FibCount := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne
  have oUW : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => h_UW hx hy
  have oWU : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := fun x hx y hy => h_WU hs hx hy
  have hO := projOnto_of summand_localization riesz_hermitian_holds
  have hgood : ∀ Λ, InFib h U 𝔭 M T Λ → Good hcU M T 𝔭 Λ := fun Λ hΛ =>
    { iU := projection_into_holds K F V hK hF h hs hnd U (orthK h U) hcU oUW M hM 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.1
      iW := projection_into_holds K F V hK hF h hs hnd (orthK h U) U hcU.symm oWU T hT 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1
        hΛ.2.2.2
      oU := hO K F V hK hF h hs hnd U (orthK h U) hcU oUW M hM 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.1
      oW := hO K F V hK hF h hs hnd (orthK h U) U hcU.symm oWU T hT 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.2
      cU := hΛ.2.2.1
      cW := hΛ.2.2.2 }
  obtain ⟨⟨⟨Λ₀, h0⟩⟩, -⟩ := Nat.card_ne_zero.mp hne
  exact card_eq hs h𝔭 hM hT hgood h0

end Formalism.L2.SG.Pf.Cnt
end
end

