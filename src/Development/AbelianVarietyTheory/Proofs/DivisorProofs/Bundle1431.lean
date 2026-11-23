module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

open Matrix GlobalTheory.SmoothForms
open GlobalTheory.Orb (archMat)

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.LeviHC.LineLie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

section Chart

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def sigA (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := A⁻¹ * Xᴴ * A
  map_add' X Y := by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    change A⁻¹ * (c • X)ᴴ * A = c • (A⁻¹ * Xᴴ * A)
    rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]

abbrev LieL (A : Matrix (Fin n) (Fin n) ℂ) : Type := ↥(GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule

def jA (A : Matrix (Fin n) (Fin n) ℂ) : LieL A →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule.subtype


open Classical in
variable (σ J) in
def secA (τ : EmbOver E w) (u : Matrix (Fin n) (Fin n) ℂ) : GAd σ J :=
  if hu : ∃ y : GArch σ J w, archMat σ J τ y = u then embArch σ J w hu.choose else 1

theorem archMat_injective (h : IsCMExt F E σ) (τ : EmbOver E w) : Function.Injective (archMat σ J τ) := fun a b e => by
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
  exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))

theorem secA_archMat (h : IsCMExt F E σ) (τ : EmbOver E w) (y : GArch σ J w) :
    secA σ J τ (archMat σ J τ y) = embArch σ J w y := by
  have hu : ∃ y' : GArch σ J w, archMat σ J τ y' = archMat σ J τ y := ⟨y, rfl⟩
  rw [secA, dite_eq_left hu, archMat_injective h τ hu.choose_spec]

theorem exists_archMat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : sigA (J.map τ.1) u * u = 1) : ∃ y : GArch σ J w, archMat σ J τ y = u := by
  have hA := isUnit_det_map hJ τ.1
  have hu1 : (J.map τ.1)⁻¹ * uᴴ * J.map τ.1 * u = 1 := hu
  have hu2 : uᴴ * J.map τ.1 * u = J.map τ.1 := by
    have := congrArg (J.map τ.1 * ·) hu1
    simpa only [← Matrix.mul_assoc, mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_one] using this
  let v : GL (Fin n) ℂ := ⟨u, (J.map τ.1)⁻¹ * uᴴ * J.map τ.1, mul_eq_one_comm.1 hu1, hu1⟩
  refine ⟨(archEquiv J h τ).symm ⟨v, show _ * _ * _ = _ from hu2⟩, ?_⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]

theorem isLieData (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    IsLieData (sigA (J.map τ.1)) (jA (J.map τ.1)) (secA σ J τ) := by
  have hA := isUnit_det_map hJ τ.1
  have hAh := conjTranspose_map h hJ τ.1
  have anti : ∀ a b, sigA (J.map τ.1) (a * b) = sigA (J.map τ.1) b * sigA (J.map τ.1) a := fun a b => by
    change _ * (a * b)ᴴ * _ = (_ * bᴴ * _) * (_ * aᴴ * _)
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hA]
  refine ⟨anti, ?_, fun a => ?_, Subtype.val_injective, fun X => ⟨fun hX => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change (J.map τ.1)⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J.map τ.1 = 1
    rw [conjTranspose_one, Matrix.mul_one, nonsing_inv_mul _ hA]
  · change _ * (_ * aᴴ * _)ᴴ * _ = a
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hAh]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hA, nonsing_inv_mul _ hA, Matrix.mul_one]
  · refine ⟨⟨X, ?_⟩, rfl⟩
    have h1 : (J.map τ.1)⁻¹ * Xᴴ * J.map τ.1 = -X := hX
    change Xᴴ * J.map τ.1 + J.map τ.1 * X = 0
    rw [← mul_nonsing_inv_cancel_left _ (Xᴴ * J.map τ.1) hA, ← Matrix.mul_assoc (J.map τ.1)⁻¹, h1, Matrix.mul_neg,
      neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    change _ * Y.1ᴴ * _ = -Y.1
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h1, Matrix.mul_neg, nonsing_inv_mul_cancel_left _ _ hA]
  · have hab : sigA (J.map τ.1) (a * b) * (a * b) = 1 := by
      rw [anti, Matrix.mul_assoc, ← Matrix.mul_assoc (sigA (J.map τ.1) a), ha, Matrix.one_mul, hb]
    obtain ⟨ya, rfl⟩ := exists_archMat h hJ τ ha
    obtain ⟨yb, rfl⟩ := exists_archMat h hJ τ hb
    rw [← map_mul, secA_archMat h, secA_archMat h, secA_archMat h, map_mul]

theorem hasLog (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    HasLog (sigA (J.map τ.1)) (jA (J.map τ.1)) :=
  GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData _ _ _ _ _ _ (isLieData h hJ τ)

theorem isLineOf_expMap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Y : LieL (J.map τ.1)) :
    IsLineOf σ J τ Y.1 fun t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y) := fun t => by
  have hA := isUnit_det_map hJ τ.1
  have hY : (t • Y.1)ᴴ * J.map τ.1 + J.map τ.1 * (t • Y.1) = 0 := by
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  have h1 : (NormedSpace.exp (t • Y.1))ᴴ * J.map τ.1 * NormedSpace.exp (t • Y.1) = J.map τ.1 :=
    GlobalTheory.SmoothForms.exp_mem_UH hA hY
  have hu : sigA (J.map τ.1) (NormedSpace.exp (t • Y.1)) * NormedSpace.exp (t • Y.1) = 1 := by
    change (J.map τ.1)⁻¹ * _ * J.map τ.1 * _ = 1
    rw [Matrix.mul_assoc _ _ (J.map τ.1), Matrix.mul_assoc, h1, nonsing_inv_mul _ hA]
  obtain ⟨y, hy⟩ := exists_archMat h hJ τ hu
  refine ⟨y, ?_, hy⟩
  change secA σ J τ (NormedSpace.exp (t • Y.1)) = _
  rw [← hy, secA_archMat h]

theorem sm_of_isSm (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {f : GAd σ J → ℂ} (hf : IsSm σ J f) :
    Sm (expMap (jA (J.map τ.1)) (secA σ J τ)) f := by
  rw [GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind _ _ _ _ _ _ (isLieData h hJ τ) (hasLog h hJ τ) Set.univ Submodule.span_univ]
  intro k Y _ g
  exact hf k (fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y i))
    (fun i => (isLineOf_expMap h hJ τ (Y i)).isRealLine h) g

end Chart

end GlobalTheory.LeviHC.LineLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionEtaleOfSquarefreeChowForm
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.HSChoice.EtaleSection

namespace GlobalTheory.HSShort.EtaleSection

theorem spec_zero_iff {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (δ : ℕ)
    (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F) (hf : IsChowForm T.imageIdeal T.D δ f)
    (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) (ξ : Fin T.N → AlgebraicClosure E) :
    eval (fun p => ξ p.2) (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) = 0 ↔
      ∃ x ∈ T.geomPts E (T.linSection E s),
        ∑ j, ξ j * T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 j = 0 := by
  rw [eval_spec]
  obtain ⟨hA, hB⟩ := _root_.GlobalTheory.ChowZeroExt.zero_set_ext F _ _ δ _ f hf
  have hs : ∀ (u y : Fin T.N → AlgebraicClosure E) (c : AlgebraicClosure E), ∑ j, u j * y j = 0 →
      ∑ j, u j * (c • y) j = 0 := fun u y c h => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum]
    rw [h, mul_zero]
  constructor
  · intro h0
    obtain ⟨y, hy, hc, h₁, h₂⟩ := hB _ _ _ h0
    obtain ⟨x₀, c, -, h⟩ := GlobalTheory.ConeOnto.exists_pt_of_mem_cone_of_isAlgClosed F T.toLinSys hT.alg.variety hT.alg.bpf _ y hy hc
    obtain ⟨x, rfl⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure E)).2 x₀
    refine ⟨x, (T.toLinSys.mem_subPts_cut_baseChange_iff E s x).2 fun i => ?_, ?_⟩ <;> rw [h]
    · exact hs _ _ _ (h₁ i)
    · exact hs _ _ _ h₂
  · rintro ⟨x, hx, h⟩
    refine hA _ _ _ _ (hT.alg.bpf.coords_ne_zero _) (fun g hg => ?_)
      ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx) h
    have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hg
    rwa [LinSys.baseHom_ptOver] at this

theorem simpleAt_of_noSquare : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → (δ : ℤ) = T.del → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite → T.InOpen E (T.linSection E s) → NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) → SimpleAt T δ f E s := by
  intro F _ _ T hT δ f hf hδ E _ _ s hfin hopen hsq
  classical
  obtain ⟨hfs, hmod, hrank⟩ := finite_finrank T hT E s hfin
  letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  haveI := hmod
  have hPfin : (T.geomPts E (T.linSection E s)).Finite := hfs.finite_subPts _
  have hcard := natCard_subPts _ _ hfs (AlgebraicClosure E)
  have hI := _root_.GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure E Γ((T.linSection E s).subscheme, ⊤)
  set P := T.geomPts E (T.linSection E s) with hPdef
  set Ω := AlgebraicClosure E
  let yv : (T.toLinSys.baseChange E).Pt Ω → Fin T.N → Ω := fun x => T.coords (LinSys.toBase x : T.Pt Ω).1
  have hyv : ∀ x, yv x ≠ 0 := fun x => hT.alg.bpf.coords_ne_zero _
  let line : (T.toLinSys.baseChange E).Pt Ω → Submodule Ω (Fin T.N → Ω) := fun x => Submodule.span Ω {yv x}
  have : Finite (line '' P) := (hPfin.image line).to_subtype
  let eR : (line '' P) ≃ Fin (Nat.card (line '' P)) := Finite.equivFin _
  have hrep : ∀ q : Fin (Nat.card (line '' P)), ∃ x ∈ P, line x = (eR.symm q : Submodule Ω (Fin T.N → Ω)) :=
    fun q => (eR.symm q).2
  choose rep hrepP hrepl using hrep
  let y : Fin (Nat.card (line '' P)) → Fin T.N → Ω := fun q => yv (rep q)
  have hinj : ∀ q q', line (rep q) = line (rep q') → q = q' := by
    intro q q' h
    apply eR.symm.injective
    apply Subtype.ext
    rw [← hrepl, ← hrepl, h]
  have hzero : ∀ ξ : Fin T.N → Ω, eval (fun p => ξ p.2) (spec (fun i j => algebraMap E Ω (s i j)) f) = 0 ↔
      ∃ q, ∑ j, ξ j * y q j = 0 := by
    intro ξ
    rw [spec_zero_iff T hT δ f hf E s ξ]
    constructor
    · rintro ⟨x, hx, h0⟩
      obtain ⟨q0, hq0⟩ : ∃ q0, eR.symm q0 = ⟨line x, x, hx, rfl⟩ := ⟨_, eR.symm_apply_apply _⟩
      refine ⟨q0, ?_⟩
      have hl : line (rep q0) = line x := by rw [hrepl, hq0]
      have hm : y q0 ∈ line x := by
        rw [← hl]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
      rw [← ha]
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ a, ← Finset.mul_sum]
      rw [h0, mul_zero]
    · rintro ⟨q, hq⟩
      exact ⟨rep q, hrepP q, hq⟩
  have hprop : ∀ q q' (c : Ω), y q' = c • y q → q = q' := by
    intro q q' c h
    have hc : c ≠ 0 := by
      rintro rfl
      exact hyv _ (by simpa using h)
    apply hinj
    change Submodule.span Ω {yv (rep q)} = Submodule.span Ω {yv (rep q')}
    rw [show yv (rep q') = c • yv (rep q) from h, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  obtain ⟨hmδ, c, hc, hfac⟩ := HyperplaneFactor.eq_C_mul_prod_lin Ω T.N δ _ _ y
    (isHomogeneous_spec _ f hf.homog) hsq (fun q => hyv _) hprop hzero
  have hPf : Finite P := hPfin.to_subtype
  have hrepinj : Function.Injective (fun q => (⟨rep q, hrepP q⟩ : P)) := fun q q' h =>
    hinj q q' (by rw [show rep q = rep q' from congrArg Subtype.val h])
  have hfr : (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = δ := hrank.trans hδ.symm
  have h1 : Nat.card P = Nat.card (Γ((T.linSection E s).subscheme, ⊤) →ₐ[E] AlgebraicClosure E) := hcard
  have h3 : Module.finrank E Γ((T.linSection E s).subscheme, ⊤) = δ := by exact_mod_cast hfr
  have hPle : Nat.card P ≤ δ := by
    have h2 := hI.2.1
    omega
  have hmP : Nat.card (Fin (Nat.card (line '' P))) ≤ Nat.card P := Nat.card_le_card_of_injective _ hrepinj
  rw [Nat.card_fin] at hmP
  have hPδ : Nat.card P = δ := by omega
  have hbij : Function.Bijective (fun q => (⟨rep q, hrepP q⟩ : P)) :=
    hrepinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; show Nat.card P ≤ _; omega)
  refine ⟨⟨⟨hfs, etale_of_algebraEtale _ _ hfs (hI.2.2 ?_)⟩, hopen⟩, ?_, ?_, c, hc, ?_⟩
  · omega
  · rw [← Nat.card_coe_set_eq]
    exact hPδ
  · intro x hx x' hx' a ha h
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    obtain ⟨q', hq'⟩ := hbij.2 ⟨x', hx'⟩
    obtain rfl : rep q = x := congrArg Subtype.val hq
    obtain rfl : rep q' = x' := congrArg Subtype.val hq'
    obtain ⟨b, hb, e⟩ := T.toLinSys.exists_coords_baseChange E (rep q).1
    obtain ⟨b', hb', e'⟩ := T.toLinSys.exists_coords_baseChange E (rep q').1
    have e₁ : b' • y q' = a • b • y q := e'.symm.trans (h.trans (congrArg (a • ·) e))
    rw [hprop q q' (b'⁻¹ * a * b) (by rw [mul_smul, mul_smul, ← e₁, inv_smul_smul₀ hb'])]
  · rw [hfac]
    congr 1
    rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
    refine finprod_mem_eq_of_bijOn rep ⟨fun q _ => hrepP q, fun q _ q' _ h => hinj q q' (by rw [h]), fun x hx => ?_⟩
      fun q _ => rfl
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨q, Set.mem_univ _, congrArg Subtype.val hq⟩

end GlobalTheory.HSShort.EtaleSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Pointwise
namespace GlobalTheory.ThetaParsevalInner

theorem setIntegral_eq_zero_of_twist {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant] (G : AddSubgroup V) [Countable G]
    {s : Set V} (hs : IsAddFundamentalDomain G s μ) {h : V → ℂ} (hper : ∀ g ∈ G, ∀ y, h (g + y) = h y)
    {c : V} {a : ℂ} (hc : ∀ y, h (c + y) = a * h y) (ha : a ≠ 1) : ∫ y in s, h y ∂μ = 0 := by
  have ht : IsAddFundamentalDomain G (c +ᵥ s) μ := hs.vadd_of_comm c
  have e1 : ∫ y in s, h y ∂μ = ∫ y in c +ᵥ s, h y ∂μ := hs.setIntegral_eq ht (fun g y => hper g g.2 y)
  have e2 : ∫ y in c +ᵥ s, h y ∂μ = ∫ y in s, h (c + y) ∂μ := by
    have := (measurePreserving_add_left μ c).setIntegral_preimage_emb (measurableEmbedding_addLeft c) h (c +ᵥ s)
    rw [← this]
    congr 2
    ext y
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e3 : ∫ y in s, h (c + y) ∂μ = a * ∫ y in s, h y ∂μ := by
    simp_rw [hc]
    exact integral_const_mul a _
  have : (1 - a) * ∫ y in s, h y ∂μ = 0 := by rw [sub_mul, one_mul, ← e3, ← e2, ← e1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem lintegral_thetaSum_schr_sq : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
      μ 𝓕₁ ≠ ⊤ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ x : (κ → AF F),
      ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
        μ 𝓕₁ * ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 := by
  intro F _ _ ψ hψ κ _ μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (κ → AF F) → ℂ, g = fun y => ∑' ξ, a ξ * e ξ y := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hconj : ∀ t, (starRingEnd ℂ) (ψ t) = ψ (-t) := fun t => by
    have h1 : ψ t * (starRingEnd ℂ) (ψ t) = 1 := by rw [Complex.mul_conj', hnorm]; simp
    have h2 : ψ t * ψ (-t) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have h0 : ψ t ≠ 0 := fun h => by simpa [h] using hnorm t
    exact mul_left_cancel₀ h0 (h1.trans h2.symm)
  have hemb_sub : ∀ ξ η, emb (ξ - η) = emb ξ - emb η := by
    intro ξ η; rw [hemb]; funext i; simp [map_sub]
  have he_sub : ∀ ξ η y, e (ξ - η) y = e ξ y * (starRingEnd ℂ) (e η y) := by
    intro ξ η y
    simp only [he]
    rw [hconj, hemb_sub, sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsum_e : ∀ y, Summable fun ξ => ‖a ξ * e ξ y‖ := fun y => by simpa [norm_mul, he_norm] using hsum
  have hg_bd : ∀ y, ‖g y‖ ≤ ∑' ξ, ‖a ξ‖ := fun y => by
    rw [hg]
    refine (norm_tsum_le_tsum_norm (hsum_e y)).trans (le_of_eq ?_)
    congr 1; funext ξ; rw [norm_mul, he_norm, mul_one]
  have hg_cont : Continuous g := by
    rw [hg]
    exact continuous_tsum (fun ξ => continuous_const.mul (he_cont ξ)) hsum
      (fun ξ y => by rw [norm_mul, he_norm, mul_one])
  have h1 : ∀ y, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ = ‖g y‖ₑ := by
    intro y
    have : GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = ψ (⅟2 * (x ⬝ᵥ y)) * g y := by
      rw [hg, ← tsum_mul_left]
      unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
      congr 1; funext ξ
      subst ha he hemb
      simp only [AddChar.map_add_eq_mul]; ring
    rw [this, enorm_mul, ← ofReal_norm_eq_enorm (ψ _), hnorm, ENNReal.ofReal_one, one_mul]
  have hgsq_int : Integrable (fun y => ‖g y‖ ^ 2) (μ.restrict 𝓕₁) :=
    Integrable.of_bound (hg_cont.norm.pow 2).aestronglyMeasurable ((∑' ξ, ‖a ξ‖) ^ 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hg_bd y) 2)
  have lhs : ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgsq_int (ae_of_all _ fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [h1, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hcomp : ∀ y, ((‖g y‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : (κ → F) × (κ → F), a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y := by
    intro y
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [hg]
    rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm (hsum_e y) (by simpa [norm_mul, he_norm] using hsum)]
    congr 1; funext p
    rw [he_sub, map_mul]; ring
  have hFint : ∀ p : (κ → F) × (κ → F),
      Integrable (fun y => a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y) (μ.restrict 𝓕₁) := fun p =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ p : (κ → F) × (κ → F),
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ = ‖a p.1‖ * ‖a p.2‖ * μ.real 𝓕₁ := by
    intro p
    simp only [norm_mul, he_norm, RCLike.norm_conj, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun p : (κ → F) × (κ → F) =>
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ := by
    simp_rw [hnormint]
    exact (hsum.mul_of_nonneg hsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
          subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ p : (κ → F) × (κ → F), ∫ y in 𝓕₁, a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y ∂μ =
      if p.1 = p.2 then ((‖a p.1‖ ^ 2 * μ.real 𝓕₁ : ℝ) : ℂ) else 0 := by
    intro p
    rw [integral_const_mul, horth]
    by_cases h : p.1 = p.2
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h, h, Complex.mul_conj']; push_cast; ring
    · rw [if_neg (sub_ne_zero.mpr h), if_neg h, mul_zero]
  have hI : ∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ = (∑' ξ, ‖a ξ‖ ^ 2) * μ.real 𝓕₁ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [hcomp]
    rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
    simp_rw [hFval]
    have hinj : Function.Injective (fun ξ : κ → F => (ξ, ξ)) := fun _ _ h => (Prod.ext_iff.1 h).1
    rw [← hinj.tsum_eq]
    · simp only [if_true]
      rw [← tsum_mul_right, Complex.ofReal_tsum]
    · intro p hp
      by_cases h : p.1 = p.2
      · exact ⟨p.1, Prod.ext rfl h⟩
      · exact absurd (if_neg h) hp
  have hsq : Summable fun ξ => ‖a ξ‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ξ => by
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hsum.le_tsum ξ (fun _ _ => norm_nonneg _)) (norm_nonneg _))
      (hsum.mul_left (∑' ξ, ‖a ξ‖))
  rw [lhs, hI, ENNReal.ofReal_mul (tsum_nonneg fun _ => sq_nonneg _), ofReal_measureReal hfin, mul_comm,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsq]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ha, hemb]

end GlobalTheory.ThetaParsevalInner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_theta_integral_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  first | exact @GlobalTheory.IntegralDetModule.modu_norm_det_triple | exact GlobalTheory.IntegralDetModule.modu_norm_det_triple | (intros; apply GlobalTheory.IntegralDetModule.modu_norm_det_triple <;> assumption)
end

