module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1754
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.AnnCompactStd

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_add (a b : Af F) : pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b := by
  refine Prod.ext ?_ rfl
  show (0 : Ainf F) = 0 + 0
  exact (add_zero 0).symm

theorem exists_psi_fin_trivial {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F,
      ψ (pairA F 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) * y)) = 1 := by
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) Circle :=
    { toFun := fun y => ⟨ψ (pairA F 0 y), mem_sphere_zero_iff_norm.2 (GlobalTheory.StdCharFromIsStd.norm_psi_fin hψ y)⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        show ψ (pairA F 0 0) = 1
        exact AddChar.map_zero_eq_one ψ
      map_add_eq_mul' := fun a b => by
        apply Subtype.ext
        show ψ (pairA F 0 (a + b)) = ψ (pairA F 0 a) * ψ (pairA F 0 b)
        rw [pairA_zero_add, AddChar.map_add_eq_mul] }
  have hχ : Continuous χ :=
    Continuous.subtype_mk (hψ.1.comp (continuous_const.prodMk continuous_id)) _
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_finiteChar_mul_eq_one χ hχ
  refine ⟨d, hd0, fun y hy => ?_⟩
  have h := congrArg (fun z : Circle => (z : ℂ)) (hd y hy)
  exact h

end GlobalTheory.AnnCompactStd

namespace GlobalTheory.AnnCompactStd

open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_mul_mem_of_forall {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ z : FiniteAdeleRing (𝓞 F) F,
      (∀ t ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (pairA F 0 (z * t)) = 1) →
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) * z ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  obtain ⟨d, hd0, hd⟩ := exists_psi_fin_trivial hψ
  obtain ⟨m, hm0, hm⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  refine ⟨m * d, mul_ne_zero (nonZeroDivisors.ne_zero hm0) hd0, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) z
  set δ : F := algebraMap (𝓞 F) F d with hδ
  have hint : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := fun a =>
    GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a
  have htr : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (k * δ * algebraMap (𝓞 F) F a) = n := by
    intro a
    have h1 := hz (algebraMap F _ δ * algebraMap F _ (algebraMap (𝓞 F) F a))
      (Subring.mul_mem _ (hint d) (hint a))
    have hsplit : z * (algebraMap F (FiniteAdeleRing (𝓞 F) F) δ *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (k * δ * algebraMap (𝓞 F) F a) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * ((z - algebraMap F _ k) *
          algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) := by
      rw [map_mul, map_mul]; ring
    rw [hsplit, pairA_zero_add, AddChar.map_add_eq_mul, hd _ (Subring.mul_mem _ hk (hint a)), mul_one,
      GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : ((Algebra.trace ℚ F (k * δ * algebraMap (𝓞 F) F a) : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at hn
      push_cast
      exact mul_right_cancel₀ hne hn
    exact_mod_cast h2
  have hdual : k * δ ∈ ((FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) := by
    rw [FractionalIdeal.coeToSubmodule_dual_one, Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨n, hn⟩ := htr b
    exact ⟨n, by rw [Algebra.traceForm_apply, hn]; simp⟩
  obtain ⟨b, hb⟩ := hm _ hdual
  have hsum : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (m * d)) * z =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F b) +
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F m) *
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * (z - algebraMap F _ k)) := by
    rw [hb, Algebra.smul_def, map_mul, map_mul, map_mul, map_mul]; ring
  rw [hsum]
  exact Subring.add_mem _ (hint b) (Subring.mul_mem _ (hint m) (Subring.mul_mem _ (hint d) hk))

end GlobalTheory.AnnCompactStd

namespace GlobalTheory.AnnCompactStd

open Topology

theorem isCompact_annihilator : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
  intro F _ _ ψ hψ κ _ L hL
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_of_forall hψ
  have hW : ∀ i, (fun y : FiniteAdeleRing (𝓞 F) F => (Pi.single i y : κ → FiniteAdeleRing (𝓞 F) F)) ⁻¹' L ∈
      𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := fun i =>
    (hL.preimage (continuous_single i)).mem_nhds (by
      show Pi.single i (0 : FiniteAdeleRing (𝓞 F) F) ∈ L
      rw [Pi.single_zero]; exact L.zero_mem)
  choose d hd0 hd using fun i => GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds (hW i)
  set e : κ → F := fun i => algebraMap (𝓞 F) F (c * d i) with he_def
  have he : ∀ i, e i ≠ 0 := fun i => by
    simp only [he_def]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (mul_ne_zero hc0 (hd0 i))
  let K : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun i =>
    (fun y => algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i)⁻¹ * y) ''
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hK : IsCompact K := isCompact_univ_pi fun i =>
    (GroundTheory.Global.isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)
  refine hK.of_isClosed_subset ?_ ?_
  · have hset : {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} =
        ⋂ y ∈ L, {x | ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
      ext x; simp
    rw [hset]
    refine isClosed_biInter fun y _ => isClosed_eq ?_ continuous_const
    exact hψ.1.comp (continuous_const.prodMk
      (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const))
  · intro x hx i _
    have hz : ∀ t ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F,
        ψ (pairA F 0 ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (d i)) * x i) * t)) = 1 := by
      intro t ht
      have h1 := hx _ (hd i t ht)
      rw [dotProduct_single] at h1
      rwa [mul_comm (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (d i))) (x i), mul_assoc]
    have h2 := hc _ hz
    refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i) * x i, ?_, ?_⟩
    · simp only [he_def, map_mul]
      rw [mul_assoc]
      exact SetLike.mem_coe.mpr h2
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i) * x i) = x i
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (he i), map_one, one_mul]

end GlobalTheory.AnnCompactStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem hermC_of_isom (G : Matrix (Fin r) (Fin r) E) {γ : GL (Fin r) E}
    (hγ : ∀ v w, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = herm G v w)
    (τ : E →+* ℂ) (v w : Fin r → ℂ) :
    hermC τ G ((γ : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E).map τ *ᵥ w) = hermC τ G v w := by
  rw [GlobalTheory.LevelCusp.hermC_of_herm (ε := 1) (fun v w => by rw [hγ, one_mul]), map_one, one_mul]

theorem lact_mem_dom_of_isom (M : TwoLevels E r U C) {γ : GL (Fin r) E}
    (hγ : ∀ v w, herm M.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = herm M.Gm v w)
    {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact γ x ∈ M.dom := fun τ => by
  have hd : ∀ i, dmin M.Gm (lact γ x) τ i = dmin M.Gm x τ i := fun i => by
    unfold dmin
    congr 1
    ext p q
    exact hermC_of_isom M.Gm hγ τ.1 (col (mat x τ) p) (col (mat x τ) q)
  refine ⟨?_, fun i => by rw [hd]; exact (hx τ).2 i⟩
  have e : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx τ).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

theorem lact_tr_mem (M : TwoLevels E r U C) (u : U) (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    lact (M.tr u c) x ∈ M.dom :=
  lact_mem_dom_of_isom M (M.tr_herm u c) hx

def Lmap (M : TwoLevels E r U C) (u : U) (c : C) (x : M.dom) : M.dom :=
  ⟨lact (M.tr u c) x.1, lact_tr_mem M u c x.2⟩

def pb (M : TwoLevels E r U C) (u : U) : (C → M.dom → ℂ) →ₐ[ℂ] (C → M.dom → ℂ) where
  toFun f := fun c x => f (u • c) (Lmap M u c x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem pb_apply (M : TwoLevels E r U C) (u : U) (f : C → M.dom → ℂ) (c : C) (x : M.dom) :
    pb M u f c x = f (u • c) (Lmap M u c x) := rfl

def IsHol (M : TwoLevels E r U C) (f : C → M.dom → ℂ) : Prop :=
  ∀ c, ∃ G : Frame M.Ψ r → ℂ, DifferentiableOn ℂ G M.dom ∧ ∀ x : M.dom, f c x = G x.1

def IsInv (M : TwoLevels E r U C) (f : C → M.dom → ℂ) : Prop :=
  ∀ c, ∀ γ ∈ (M.comp c).Γ, ∀ (x : M.dom) (hx : lact γ x.1 ∈ M.dom), f c ⟨lact γ x.1, hx⟩ = f c x

def HA (M : TwoLevels E r U C) : Subalgebra ℂ (C → M.dom → ℂ) where
  carrier := {f | IsHol M f ∧ IsInv M f}
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
    · obtain ⟨F, hF, hF'⟩ := hf c
      obtain ⟨G, hG, hG'⟩ := hg c
      exact ⟨F * G, hF.mul hG, fun x => by simp [hF', hG']⟩
    · simp only [Pi.mul_apply]
      rw [hf' c γ hγ x hx, hg' c γ hγ x hx]
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
    · obtain ⟨F, hF, hF'⟩ := hf c
      obtain ⟨G, hG, hG'⟩ := hg c
      exact ⟨F + G, hF.add hG, fun x => by simp [hF', hG']⟩
    · simp only [Pi.add_apply]
      rw [hf' c γ hγ x hx, hg' c γ hγ x hx]
  algebraMap_mem' := by
    intro z
    refine ⟨fun c => ⟨fun _ => z, differentiableOn_const z, fun x => rfl⟩, fun c γ hγ x hx => rfl⟩

theorem pb_mem (M : TwoLevels E r U C) (u : U) {f : C → M.dom → ℂ} (hf : f ∈ HA M) : pb M u f ∈ HA M := by
  obtain ⟨hf, hf'⟩ := hf
  refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
  · obtain ⟨G, hG, hG'⟩ := hf (u • c)
    refine ⟨fun y => G (lact (M.tr u c) y),
      hG.comp (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiable_lact _).differentiableOn (fun y hy => lact_tr_mem M u c hy),
      fun x => ?_⟩
    rw [pb_apply, hG']
    rfl
  · have hδ : M.tr u c * γ * (M.tr u c)⁻¹ ∈ (M.comp (u • c)).Γ := (M.tr_conj u c γ).1 hγ
    have e : lact (M.tr u c) (lact γ x.1) = lact (M.tr u c * γ * (M.tr u c)⁻¹) (lact (M.tr u c) x.1) := by
      simp only [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr u c)⁻¹ (M.tr u c),
        inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    have hy : lact (M.tr u c * γ * (M.tr u c)⁻¹) (Lmap M u c x).1 ∈ M.dom := by
      show lact (M.tr u c * γ * (M.tr u c)⁻¹) (lact (M.tr u c) x.1) ∈ M.dom
      rw [← e]; exact lact_tr_mem M u c hx
    rw [pb_apply, pb_apply, ← hf' (u • c) _ hδ (Lmap M u c x) hy]
    congr 1
    exact Subtype.ext e

def pbA (M : TwoLevels E r U C) (u : U) : HA M →ₐ[ℂ] HA M where
  toFun f := ⟨pb M u f, pb_mem M u f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def cst (M : TwoLevels E r U C) (a : C → ℂ) : HA M :=
  ⟨fun c _ => a c, fun c => ⟨fun _ => a c, differentiableOn_const _, fun _ => rfl⟩, fun _ _ _ _ _ => rfl⟩

def tw (M : TwoLevels E r U C) (a : C → ℂ) (u : U) : Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M) :=
  { Polynomial.eval₂RingHom (Polynomial.C.comp (pbA M u).toRingHom) (Polynomial.C (cst M a) * Polynomial.X) with
    commutes' := fun z => by
      show Polynomial.eval₂ _ _ (algebraMap ℂ (Polynomial (HA M)) z) = _
      rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
      simp }

theorem tw_C (M : TwoLevels E r U C) (a : C → ℂ) (u : U) (f : HA M) :
    tw M a u (Polynomial.C f) = Polynomial.C (pbA M u f) := by
  show Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_C]
  rfl

theorem tw_X (M : TwoLevels E r U C) (a : C → ℂ) (u : U) :
    tw M a u Polynomial.X = Polynomial.C (cst M a) * Polynomial.X := by
  show Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_X]

theorem tw_monomial_one (M : TwoLevels E r U C) (a : C → ℂ) (u : U) (f : HA M) :
    tw M a u (Polynomial.monomial 1 f) = Polynomial.monomial 1 (cst M a * pbA M u f) := by
  rw [← Polynomial.C_mul_X_eq_monomial, map_mul, tw_C, tw_X, ← mul_assoc, ← Polynomial.C_mul, mul_comm (pbA M u f),
    Polynomial.C_mul_X_eq_monomial]

end GlobalTheory.CuspEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafShareIOfShareW
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.ShareOn.Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tied

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst}

theorem card_comap_base (h1 : R.grp_levels F) : Nat.card (F.P0.comap (mirIncl R)) = Nat.card F.P0 := by
  refine Nat.card_congr (Equiv.ofBijective (fun u : F.P0.comap (mirIncl R) => (⟨mirIncl R u, u.2⟩ : F.P0)) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (mirIncl_injective R (congrArg Subtype.val hab))
  · rintro ⟨g, hg⟩
    obtain ⟨u, -, rfl⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨⟨u, hg⟩, rfl⟩

variable {P : Type} [Group P] [Finite P]

theorem mem_eig_iff {O : OnObj ((R.toCx F).data F.cr false) P c} {inc : P →* G} (h1 : R.grp_levels F) (h2 : R.grp_chiW)
    (hinc : F.P0 ≤ inc.range) (j : Fin D.R.m) (w : (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL))
    (hρ : ∀ g x, w (O.ρ j g x) = (R.FW j).ρ (inc g) (w x)) (hU : O.U = F.P0.comap inc)
    (hψ : ∀ (g : P) (hg : inc g ∈ F.P0), ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) = (F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ))
    (x : Fin (O.nZ j) → D.what₂.LL) : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ ↔ w x ∈ GlobalTheory.CovTop.spType R F j := by
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ ↔ ∀ u : O.U, O.ρ j u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ j g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW j).ρ (inc g) (w x) = (((R.FW j).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • w x :=
    fun g hg => by
      rw [chi_eq_one h1 h2 j hg, one_mul, ← hψ g hg, ← hρ, ← LinearEquiv.map_smul, w.injective.eq_iff]
  show _ ↔ ∀ q : F.P0, (R.FW j).ρ q (w x) = (((R.FW j).chi q * F.ψ0⁻¹ q : D.what₂.LLˣ) : D.what₂.LL) • w x
  refine e1.trans ⟨?_, fun h u => ?_⟩
  · rintro h ⟨g, hg⟩
    obtain ⟨q, rfl⟩ := hinc hg
    exact (e2 q hg).1 (h ⟨q, hU ▸ hg⟩)
  · have hg : inc u ∈ F.P0 := (hU ▸ u.2 : (u : P) ∈ F.P0.comap inc)
    exact (e2 u hg).2 (h ⟨inc u, hg⟩)

theorem tied_dims {O : OnObj ((R.toCx F).data F.cr false) (Mir R) c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph (mirIncl R) O) (h1 : R.grp_levels F) (h2 : R.grp_chiW)
    (j : Fin D.R.m) :
    O.nZ j = R.nW j ∧ Nat.card O.U = Nat.card F.P0 ∧ O.d0 j = (finrank D.what₂.LL (GlobalTheory.CovTop.spType R F j) : ℝ) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v, -⟩ := exists_place3 D.what₂.LL
  have t := (ht v j).1
  let w : (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) :=
    LinearEquiv.ofBijective (toForms (T := (run v).full) (R := R) (h v) fw j (z j))
      (toForms_bijective (T := (run v).full) (R := R) (h v) fw j (z j))
  have hinc : F.P0 ≤ (mirIncl R).range := fun g hg => by
    obtain ⟨u, -, rfl⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · have := w.finrank_eq
    simpa only [Module.finrank_fin_fun] using this
  · rw [t.U_eq]
    exact card_comap_base h1
  · have hm : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).map (w : (Fin (O.nZ j) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL)) =
        GlobalTheory.CovTop.spType R F j := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (mem_eig_iff h1 h2 hinc j w (t.rho_eq_of_actionPin (ht v j).2) t.U_eq t.ψ_eq x).1 hx
      · intro hu
        refine ⟨w.symm u, ?_, w.apply_symm_apply u⟩
        refine (mem_eig_iff h1 h2 hinc j w (t.rho_eq_of_actionPin (ht v j).2) t.U_eq t.ψ_eq _).2 ?_
        rw [w.apply_symm_apply]
        exact hu
    unfold OnObj.d0
    rw [← hm, LinearEquiv.finrank_map_eq]

end Tied

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem leafShareI_of_shareW (p : PtAt ex Csz) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hR : RecAt p Tp r O) (hW : ∀ i, ShareW p i (1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3))) :
    LeafShareI O := by
  have hfk : O.f = (D.R.f : ℝ) ∧ O.k = (D.R.k : ℝ) := by
    letI := hostAlg D
    obtain ⟨st, rt⟩ := hR.1.depth
    exact ⟨rt.f_eq, rt.k_eq⟩
  obtain ⟨hc, hinj, ht⟩ := hR.1.tied
  intro j
  obtain ⟨hn, hU, hd⟩ := tied_dims ht p.charW.base.grp.levels p.charW.base.grp.chiW j
  refine ⟨O.y, le_rfl, ?_⟩
  have hy : O.y = 1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3) := by
    unfold OnObj.y
    rw [hfk.1, hfk.2]
  have hw := hW j
  unfold ShareW at hw
  rw [hy, hn, hd, hU]
  exact hw

end Point

end GlobalTheory.ShareOn.Comparison₂

namespace GlobalTheory.ShareOn

end GlobalTheory.ShareOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEigenvalueLowerBoundOfWeakCharacterisation
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow

theorem lamLow_of_weak : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCR D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH hOk hsep hC hEx prim hph hstd fw hbar hio hpins hrow0 htie hsz hlow hnum hAd hPH
  obtain ⟨hcore, hok, hlinks⟩ := _root_.GlobalTheory.LowRow.baseLinks_of_prims R F s hOk hsep hC hEx prim hph
  have hgal : ∀ i, GalOut R.toRealDat i 1 := fun i =>
    hCR D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O 1 (GlobalTheory.Core5.of_core hcore) hstd fw hbar hio prim.unif hpins i (by
      have h1 := htie i prim.unif (hrow0 i)
      simp only [hph] at h1
      simpa using h1)
  have hext : ∀ i σ, ∃ v : (R.toRealDat.MW i σ).Vec, IsExtVec (R.toRealDat.MW i σ) v := fun i σ => ⟨v₀ i σ, (fw.hv₀ i σ).1⟩
  have htop := _root_.GlobalTheory.LowTopCore.lowTop_ofCore R.toRealDat F.lv2 s b hAd hcore hok hPH hsz
  have hform := GlobalTheory.T.rationalLift_lowerBound_off_basePlace R.toRealDat F.lv2 s b hAd hgal hcore hok hext prim.unif hlinks hPH hsz
  have h0 := _root_.GlobalTheory.LowRow.l6m_le_log_lam3_base_place R F b hC prim.thmA prim.posScal htop hlow
  have h1 := _root_.GlobalTheory.LowOff.l6m_le_log_lam3_other_places R F b hC hph prim.posScal prim.scalConj hform hlow
  intro j p v
  have hn := hnum j
  by_cases hv : v = A3.A.v0
  · subst hv
    have := h0 j p
    exact le_trans hn this
  · have := h1 j p v hv
    exact le_trans hn this

end GlobalTheory.LowRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnClausesWithErrorOfSplitPartStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onClauses_with_error_of_splitPart : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), ∀ (C CH : ℝ) (err : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ), ONwith (S2 p) ((R2 p).num (F2 p) C CH) err → ONwith (p.S false) (p.N C CH) err ∧ (p.S false).D = (S2 p).D := by
  first | exact @GlobalTheory.BigOn.onWith_of_split | exact GlobalTheory.BigOn.onWith_of_split | (intros; apply GlobalTheory.BigOn.onWith_of_split <;> assumption)
end

