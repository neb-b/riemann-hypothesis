module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatFrameOfIsShortGen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem exists_latFrame_of_isShortGen : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (Nm : (F →+* ℂ) → V → ℝ) (M : Submodule (𝓞 F) V) (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), Nonempty (LatFrame Nm M) → CompHt.IsShortGen Nm M w abelian₂ → ∃ f : LatFrame Nm M, f.n = n ∧ (∀ x ∈ Submodule.span (𝓞 F) (Set.range f.w.col), x ∈ Submodule.span ℤ (Set.range f.w.col)) ∧ ∀ i σ, ChowHt.frameNorm (f.A σ) (fun a => σ (f.w.col i a)) ≤ abelian₂ := by
  intro F V _ _ _ _ _ _ Nm M n w abelian₂ hf hw
  obtain ⟨f⟩ := hf
  classical
  let e := f.b.equivFun
  let w' : Matrix (Fin f.N) (Fin n) F := Matrix.of fun j k => e (w k) j
  have hcol : w'.col = fun k => e (w k) := rfl
  have hmemM : ∀ i, w i ∈ M := fun i => (hw.gen (w i)).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hspanO : Submodule.span (𝓞 F) (Set.range w) = M := by
    refine le_antisymm (Submodule.span_le.2 ?_) fun x hx => ?_
    · rintro _ ⟨i, rfl⟩; exact hmemM i
    · have hz := (hw.gen x).1 hx
      exact Submodule.span_le_restrictScalars ℤ (𝓞 F) _ hz
  have hsum : ∀ k, (∑ j, w' j k • f.b j) = w k := fun k => by
    simp only [w', Matrix.of_apply, e, Module.Basis.equivFun_apply, Module.Basis.sum_repr]
  have hfullV : Submodule.span F (Set.range w) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← f.isFull.2]
    refine Submodule.span_le.2 fun x hx => ?_
    have hz := (hw.gen x).1 hx
    exact Submodule.span_le_restrictScalars ℤ F _ (Submodule.span_mono (le_refl _) hz)
  refine ⟨⟨f.N, n, f.b, w', f.A, ⟨?_, ?_, f.isFrame.herm, f.isFrame.conj, f.isFrame.norm⟩⟩, rfl, ?_, ?_⟩
  · simp only [hsum]; exact hspanO
  · rw [hcol, Set.range_comp', show (⇑e '' Set.range w) = (e.toLinearMap) '' Set.range w from rfl,
      Submodule.span_image, hfullV, Submodule.map_top, LinearEquiv.range]
  · intro x hx
    let eO : V →ₗ[𝓞 F] (Fin f.N → F) := e.toLinearMap.restrictScalars (𝓞 F)
    let eZ : V →ₗ[ℤ] (Fin f.N → F) := e.toLinearMap.restrictScalars ℤ
    have hO : Submodule.span (𝓞 F) (Set.range w'.col) = (Submodule.span (𝓞 F) (Set.range w)).map eO := by
      rw [Submodule.map_span, hcol, Set.range_comp']; rfl
    have hZ : Submodule.span ℤ (Set.range w'.col) = (Submodule.span ℤ (Set.range w)).map eZ := by
      rw [Submodule.map_span, hcol, Set.range_comp']; rfl
    rw [hO] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hZ]
    exact ⟨y, (hw.gen y).1 (hspanO ▸ hy), rfl⟩
  · intro i σ
    show ChowHt.frameNorm (f.A σ) (fun a => σ (e (w i) a)) ≤ abelian₂
    simp only [e, Module.Basis.equivFun_apply]
    rw [f.isFrame.norm σ (w i)]
    exact hw.le i σ

end GlobalTheory.HSApp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
section
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Mul

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G₀ : WTZ E}

theorem mul_idem_cusp {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * idem Z = f := by
  rw [mul_comm]; exact idem_mul_eq (e := exZ Dw G) ⟨cuspW_le_secZ G hf.1, hf.2⟩

def mulEquiv (s : TwSec U x Z G₀) (G : WTZ E) (hG : Even G.2) : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀) where
  toFun f := ⟨(f : Rul Xo c) * s.sig, s.cusp_sig G hG f f.2⟩
  invFun g := ⟨(g : Rul Xo c) * s.inv, s.cusp_inv G hG g g.2⟩
  map_add' f f' := Subtype.ext (add_mul _ _ _)
  map_smul' a f := Subtype.ext (smul_mul_assoc a (f : Rul Xo c) s.sig)
  left_inv f := Subtype.ext (by
    show (f : Rul Xo c) * s.sig * s.inv = f
    rw [mul_assoc, s.mul_inv, mul_idem_cusp f.2])
  right_inv g := Subtype.ext (by
    show (g : Rul Xo c) * s.inv * s.sig = g
    rw [mul_assoc, mul_comm s.inv, s.mul_inv, mul_idem_cusp g.2])

theorem ereal_nonneg {a b : ℝ} {t : EReal} (ht : 0 ≤ t) (hab : 0 ≤ a + b) :
    0 ≤ ((a : ℝ) : EReal) + (t + ((b : ℝ) : EReal)) := by
  rw [add_comm t, ← add_assoc, ← EReal.coe_add]
  exact add_nonneg (EReal.coe_nonneg.2 hab) ht

theorem mem_latOn_of_mul (s : TwSec U x Z G₀) {G G' : WTZ E} (a : c.F) (ha : a ≠ 0)
    (hlo : ∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) (f : cuspOn U Z G) (hf : f ∈ latOn U Z G)
    (g : cuspOn U Z G') (hg : (g : Rul Xo c) = a • ((f : Rul Xo c) * s.sig)) : g ∈ latOn U Z G' := by
  refine (mem_supLat_iff (Z := Z) g.2.2).2 fun w v hv => ?_
  have hfv : 0 ≤ v (f : Rul Xo c) := ((mem_supLat_iff (Z := Z) f.2.2).1 hf) w v hv
  obtain ⟨b, hb, -, hlb, -⟩ := s.exists_val hv
  rw [hg, (isVal_valOn hv).smul _ _ ha, (isVal_valOn hv).mul, hb]
  exact ereal_nonneg hfv (by linarith [hlo w])

theorem mem_latOn_of_mul_inv (s : TwSec U x Z G₀) {G G' : WTZ E} (b : c.F) (hb : b ≠ 0)
    (hhi : ∀ w, s.hi w ≤ (vAdd w b : ℝ)) (g : cuspOn U Z G') (hg : g ∈ latOn U Z G')
    (f : cuspOn U Z G) (hf : (f : Rul Xo c) = b • ((g : Rul Xo c) * s.inv)) : f ∈ latOn U Z G := by
  refine (mem_supLat_iff (Z := Z) f.2.2).2 fun w v hv => ?_
  have hgv : 0 ≤ v (g : Rul Xo c) := ((mem_supLat_iff (Z := Z) g.2.2).1 hg) w v hv
  obtain ⟨β, -, hβ, -, hβh⟩ := s.exists_val hv
  rw [hf, (isVal_valOn hv).smul _ _ hb, (isVal_valOn hv).mul, hβ]
  exact ereal_nonneg hgv (by linarith [hhi w])

theorem twSec_mulEquiv_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∃ φ : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀), (∀ f, (φ f : Rul Xo c) = f * s.sig) ∧ (∀ g, (φ.symm g : Rul Xo c) = g * s.inv) ∧ (∀ a : c.F, a ≠ 0 → (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) → ∀ f ∈ latOn U Z G, ∀ g : cuspOn U Z (G + G₀), (g : Rul Xo c) = a • (φ f : Rul Xo c) → g ∈ latOn U Z (G + G₀)) ∧ (∀ b : c.F, b ≠ 0 → (∀ w, s.hi w ≤ (vAdd w b : ℝ)) → ∀ g ∈ latOn U Z (G + G₀), ∀ f : cuspOn U Z G, (f : Rul Xo c) = b • (φ.symm g : Rul Xo c) → f ∈ latOn U Z G) := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG
  refine ⟨mulEquiv s G hG, fun _ => rfl, fun _ => rfl, fun a ha hlo f hf g hg => ?_, fun b hb hhi g hg f hf => ?_⟩
  · exact mem_latOn_of_mul s a ha hlo f hf g hg
  · exact mem_latOn_of_mul_inv s b hb hhi g hg f hf

end GlobalTheory.FlatTw.Mul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModuliPointTrivSqZeroExtTangentBasis
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TanBasis

open TensorProduct

theorem exists_tan_basis {R A K ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Fintype ι] {n : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (xr : A →+* K) (hι : Fintype.card ι = n) :
    ∃ Φ : A →+* TrivSqZeroExt K (ι → K), (∀ a, (Φ a).fst = xr a) ∧ (∀ r, (Φ (algebraMap R A r)).snd = 0) ∧
      ∀ M M' : ι → K, (∀ a, ∑ k, (Φ a).snd k * M k = ∑ k, (Φ a).snd k * M' k) → M = M' := by
  classical
  haveI := GlobalTheory.AugCot.smooth_of_locally h
  letI : Algebra A K := xr.toAlgebra
  have hrank : Module.finrank K (K ⊗[A] Ω[A⁄R]) = n := by
    have h1 := Module.rankAtStalk_baseChange (R := A) (M := Ω[A⁄R]) (S := K) (IsLocalRing.closedPoint K)
    rw [Module.rankAtStalk_eq_finrank_of_free, GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally h] at h1
    exact_mod_cast h1
  let b : Module.Basis ι K (K ⊗[A] Ω[A⁄R]) :=
    (Module.finBasisOfFinrankEq K _ hrank).reindex (Fintype.equivFinOfCardEq hι).symm
  let δ : A → (ι → K) := fun a => b.equivFun (1 ⊗ₜ KaehlerDifferential.D R A a)
  have hsm : ∀ (a : A) (m : Ω[A⁄R]), (1 : K) ⊗ₜ[A] (a • m) = xr a • ((1 : K) ⊗ₜ[A] m) := by
    intro a m
    rw [TensorProduct.tmul_smul, ← algebraMap_smul K a]
    rfl
  have hδmul : ∀ a a', δ (a * a') = xr a • δ a' + xr a' • δ a := by
    intro a a'
    simp only [δ, Derivation.leibniz, TensorProduct.tmul_add, hsm, map_add (f := _), map_smul]
  have hδadd : ∀ a a', δ (a + a') = δ a + δ a' := by
    intro a a'; simp only [δ, map_add (f := _), TensorProduct.tmul_add]
  have hδalg : ∀ r, δ (algebraMap R A r) = 0 := by
    intro r; simp only [δ, Derivation.map_algebraMap, TensorProduct.tmul_zero, map_zero]
  have hδ1 : δ 1 = 0 := by simpa using hδalg 1
  have hδ0 : δ 0 = 0 := by simp only [δ, map_zero, TensorProduct.tmul_zero]
  let Φ : A →+* TrivSqZeroExt K (ι → K) :=
    { toFun := fun a => TrivSqZeroExt.inl (xr a) + TrivSqZeroExt.inr (δ a)
      map_one' := by ext <;> simp [hδ1]
      map_mul' := fun a a' => by
        ext k
        · simp
        · simp [hδmul, TrivSqZeroExt.snd_mul, add_comm]
      map_zero' := by ext <;> simp [hδ0]
      map_add' := fun a a' => by ext <;> simp [hδadd] }
  refine ⟨Φ, fun a => by simp [Φ], fun r => by simp [Φ, hδalg], fun M M' hM => ?_⟩
  let L : (ι → K) → (K ⊗[A] Ω[A⁄R] →ₗ[K] K) := fun M => Fintype.linearCombination K M ∘ₗ b.equivFun.toLinearMap
  have hL : ∀ M : ι → K, ∀ a, L M (1 ⊗ₜ KaehlerDifferential.D R A a) = ∑ k, (Φ a).snd k * M k := by
    intro M a
    simp [L, Φ, δ, Fintype.linearCombination_apply, smul_eq_mul]
  have hLL : L M = L M' := by
    apply (LinearMap.liftBaseChangeEquiv K).symm.injective
    refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A) fun a => ?_
    rw [LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.liftBaseChangeEquiv_symm_apply, hL, hL, hM]
  funext j
  have := LinearMap.congr_fun hLL (b j)
  simpa [L, Finsupp.single_eq_pi_single, Fintype.linearCombination_apply_single] using this

end GlobalTheory.TanBasis

namespace GlobalTheory.TanBasis

theorem exists_point_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι], Fintype.card ι = Dw.dim → ∃ X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x ∧ Function.Injective (fun M : ι → K => spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  intro E _ _ _ H Dw l Xo c K _ _ y ι _ hι
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y.x (IsLocalRing.closedPoint K)) (U := ⊤) trivial
  have hrange : Set.range y.x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]
  let y' := IsOpenImmersion.lift hU.fromSpec y.x hrange
  have hy' : y' ≫ hU.fromSpec = y.x := IsOpenImmersion.lift_fac _ _ _
  let g := Spec.preimage (hU.fromSpec ≫ Xo.s)
  have hg : Spec.map g = hU.fromSpec ≫ Xo.s := Spec.map_preimage _
  let xr := Spec.preimage y'
  have hxr : Spec.map xr = y' := Spec.map_preimage _
  haveI := Xo.smooth
  have hsm : SmoothOfRelativeDimension Dw.dim (Spec.map g) := by
    rw [hg]
    have := (inferInstance : SmoothOfRelativeDimension (0 + Dw.dim) (hU.fromSpec ≫ Xo.s))
    rwa [zero_add] at this
  have hloc := HasRingHomProperty.Spec_iff.1 hsm
  letI : Algebra (KA l) Γ(Xo.X, U) := g.hom.toAlgebra
  obtain ⟨Φ, h1, h2, h3⟩ := exists_tan_basis (R := KA l) (A := Γ(Xo.X, U)) hloc xr.hom hι
  have hbase : ∀ r, xr.hom (g.hom r) = algebraMap c.F K (IntermediateField.inclusion c.le r) := by
    have : Spec.map (g ≫ xr) = sOf c K := by
      rw [Spec.map_comp, hxr, hg, ← Category.assoc, hy', y.x_over]
    intro r
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective this)) r
  have hfst : (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom.comp Φ = xr.hom := by
    ext a; exact h1 a
  refine ⟨spMap Φ ≫ hU.fromSpec, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hg, spMap, ← Spec.map_comp, sOf]
    have hΦg : Φ.comp g.hom =
        (algebraMap c.F (TrivSqZeroExt K (ι → K))).comp (IntermediateField.inclusion c.le).toRingHom := by
      refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
      · rw [RingHom.comp_apply, h1, hbase]
        simp [TrivSqZeroExt.algebraMap_eq_inl']
      · rw [RingHom.comp_apply, show g.hom r = algebraMap (KA l) Γ(Xo.X, U) r from rfl, h2]
        simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [← hΦg]
    rfl
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom.comp Φ)) ≫ _ = _
    rw [hfst]
    change Spec.map xr ≫ _ = _
    rw [hxr, hy']
  · intro M M' hMM
    simp only at hMM
    rw [← Category.assoc, ← Category.assoc, cancel_mono, spMap, spMap, spMap, ← Spec.map_comp,
      ← Spec.map_comp] at hMM
    have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hMM)
    apply h3
    intro a
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hr a)
    simpa using this

end GlobalTheory.TanBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomOverAlgebraicClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ChowRigid

open GlobalTheory.Spread

theorem factor_finite (K B E : Type) [Field K] [CommRing B] [CommRing E] [Algebra K B] [Algebra K E]
    (i : E →ₐ[K] B) (hι : Function.Injective i) (hint : ∀ b : B, _root_.IsIntegral K b → b ∈ i.range)
    (T : Scheme.{0}) (p : T ⟶ Sp K) [IsFinite p] (t : Sp B ⟶ T) (ht : t ≫ p = spMap (algebraMap K B)) :
    ∃ u : Sp E ⟶ T, u ≫ p = spMap (algebraMap K E) ∧ t = spMap i.toRingHom ≫ u :=
  _root_.GlobalTheory.point_factor_integral_subalgebra K B E i hι hint T p t ht

theorem torsion_factor (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : 0 < n) (B E : Type) [CommRing B] [CommRing E] [Algebra K B] [Algebra K E]
    (i : E →ₐ[K] B) (hι : Function.Injective i) (hint : ∀ b : B, IsIntegral K b → b ∈ i.range)
    (T : Over (Sp K)) (y : T ⟶ A) (hy : y ^ n = 1) (t : Sp B ⟶ T.left)
    (ht : t ≫ T.hom = spMap (algebraMap K B)) :
    ∃ x : Over.mk (spMap (algebraMap K E)) ⟶ A, x ^ n = 1 ∧ t ≫ y.left = spMap i.toRingHom ≫ x.left := by
  have := hA.comm; have := hA.smooth; have := hA.proper
  have hu : IsUnit ((n : Γ(Sp K, ⊤))) := by
    have : IsUnit (n : K) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have := GlobalTheory.GrpTangent.isFinite_torsion A hu
  obtain ⟨hη1, huniv⟩ := GlobalTheory.LamF.torsion_universal A n
  obtain ⟨w, hw⟩ := huniv T y hy
  obtain ⟨u, hu1, hu2⟩ := factor_finite K B E i hι hint (torsion A n).left (torsion A n).hom (t ≫ w.left)
    (by rw [Category.assoc, Over.w w, ht])
  refine ⟨Over.homMk u hu1 ≫ torsion.ι A n, ?_, ?_⟩
  · rw [← comp_pow, hη1, comp_one]
  · rw [← hw, Over.comp_left, ← Category.assoc, hu2, Over.comp_left, Category.assoc]
    rfl

theorem compare (K Ω : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (S : Type) [CommRing S] [Algebra K S]
    (i : algebraicClosure K Ω →ₐ[K] S) (j : S →ₐ[K] Ω) (ρ : S →ₐ[K] algebraicClosure K Ω)
    (hj : Function.Injective j) (hji : ∀ x, j (i x) = x) (hρi : ∀ x, ρ (i x) = x)
    (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    (gS : (Over.pullback (spMap (algebraMap K S))).obj A ⟶ (Over.pullback (spMap (algebraMap K S))).obj A')
    [IsMonHom gS]
    (g : (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A ⟶
      (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A')
    [IsMonHom g] (hg : g.left ≫ pullback.fst _ _ = bcMap A.hom ρ ≫ gS.left ≫ pullback.fst _ _) :
    bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ =
      bcMap A.hom j ≫ gS.left ≫ pullback.fst _ _ := by
  have hι : Function.Injective i := fun a b h => Subtype.ext (by rw [← hji a, ← hji b, h])
  have hint : ∀ s : S, _root_.IsIntegral K s → s ∈ i.range := fun s hs => by
    have h1 : j s ∈ (algebraicClosure K Ω) := mem_algebraicClosure_iff'.mpr (hs.map j)
    exact ⟨⟨j s, h1⟩, hj (hji _)⟩
  have hintΩ : ∀ b : Ω, _root_.IsIntegral K b → b ∈ (algebraicClosure K Ω).val.range := fun b hb =>
    ⟨⟨b, mem_algebraicClosure_iff'.mpr hb⟩, rfl⟩
  have hLinj : Function.Injective (algebraicClosure K Ω).val := Subtype.val_injective
  obtain ⟨h, hh, hhe⟩ := GlobalTheory.HomDescent.exists_specialise g (algebraicClosure K Ω).val
  obtain ⟨f, hf, hfe⟩ := GlobalTheory.HomDescent.exists_specialise gS j
  have semi := isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj (spMap (algebraMap K Ω)) A hA)
  have semi' := isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj (spMap (algebraMap K Ω)) A' hA')
  have e : f = h := by
    have := hf; have := hh
    refine GlobalTheory.HomExtNormal.hom_eq_of_torsion semi semi' f h fun y n hn hy => ?_

    let P := pushHom (isGrpPullback_pullback A (spMap (algebraMap K Ω))) (𝟙_ (Over (Sp Ω)))
    have hPn : P y ^ n = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨x, hxn, hx⟩ := torsion_factor K A hA n hn Ω (algebraicClosure K Ω) (algebraicClosure K Ω).val hLinj hintΩ _ (P y) hPn (𝟙 _) (by
      change 𝟙 _ ≫ 𝟙 _ ≫ _ = _; simp)
    have hx' : y.left ≫ pullback.fst _ _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ x.left := by
      rw [← hx, Category.id_comp]; rfl
    have hys : y.left ≫ pullback.snd _ _ = 𝟙 _ := Over.w y
    have hxw : x.left ≫ A.hom = spMap (algebraMap K (algebraicClosure K Ω)) := Over.w x
    have eji : spMap j.toRingHom ≫ spMap i.toRingHom = spMap (algebraicClosure K Ω).val.toRingHom := by
      rw [GlobalTheory.HomDescent.spMap_comp]; congr 1; exact RingHom.ext hji
    have eρi : spMap ρ.toRingHom ≫ spMap i.toRingHom = 𝟙 _ := by
      rw [GlobalTheory.HomDescent.spMap_comp, show ρ.toRingHom.comp i.toRingHom = RingHom.id _ from RingHom.ext hρi]
      exact Spec.map_id _
    let xS : Sp S ⟶ pullback A.hom (spMap (algebraMap K S)) :=
      pullback.lift (spMap i.toRingHom ≫ x.left) (𝟙 _) (by
        rw [Category.assoc, hxw, Category.id_comp, spMap_algHom_comp])
    let xL : Sp (algebraicClosure K Ω) ⟶ pullback A.hom (spMap (algebraMap K (algebraicClosure K Ω))) :=
      pullback.lift x.left (𝟙 _) (by rw [hxw, Category.id_comp])
    have c1 : y.left ≫ bcMap A.hom j = spMap j.toRingHom ≫ xS := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, hx', Category.assoc, pullback.lift_fst, ← Category.assoc, eji]
      · rw [Category.assoc, bcMap_snd, ← Category.assoc, hys, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have c2 : y.left ≫ bcMap A.hom (algebraicClosure K Ω).val = spMap (algebraicClosure K Ω).val.toRingHom ≫ xL := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, hx', Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, bcMap_snd, ← Category.assoc, hys, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have c3 : xL ≫ bcMap A.hom ρ = spMap ρ.toRingHom ≫ xS := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
          eρi, Category.id_comp]
      · rw [Category.assoc, bcMap_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]

    let xS' : 𝟙_ (Over (Sp S)) ⟶ (Over.pullback (spMap (algebraMap K S))).obj A :=
      Over.homMk xS (pullback.lift_snd _ _ _)
    let PS := pushHom (isGrpPullback_pullback A (spMap (algebraMap K S))) (𝟙_ (Over (Sp S)))
    have hPSinj : Function.Injective PS := fun a b e =>
      Over.OverMorphism.ext ((isGrpPullback_pullback A (spMap (algebraMap K S))).1.hom_ext
        (congrArg (fun z => z.left) e) (by rw [Over.w a, Over.w b]))
    let q : Over.mk ((𝟙_ (Over (Sp S))).hom ≫ spMap (algebraMap K S)) ⟶ Over.mk (spMap (algebraMap K (algebraicClosure K Ω))) :=
      Over.homMk (spMap i.toRingHom) (by
        change _ = 𝟙 _ ≫ _
        rw [Category.id_comp]; exact spMap_algHom_comp i)
    have hPS : PS xS' = q ≫ x := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have hxSn : xS' ^ n = 1 := hPSinj (by rw [map_pow, hPS, ← comp_pow, hxn, comp_one, map_one])
    let P' := pushHom (isGrpPullback_pullback A' (spMap (algebraMap K S))) (𝟙_ (Over (Sp S)))
    have hzn : P' (xS' ≫ gS) ^ n = 1 := by rw [← map_pow, ← pow_comp, hxSn, one_comp, map_one]
    obtain ⟨c, -, hc⟩ := torsion_factor K A' hA' n hn S (algebraicClosure K Ω) i hι hint _ (P' (xS' ≫ gS)) hzn (𝟙 _) (by
      change 𝟙 _ ≫ 𝟙 _ ≫ _ = _; simp)
    have hz : xS ≫ gS.left ≫ pullback.fst _ _ = spMap i.toRingHom ≫ c.left := by
      rw [← hc, Category.id_comp]; rfl
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [hfe, hhe]
      calc y.left ≫ bcMap A.hom j ≫ gS.left ≫ pullback.fst _ _
          = spMap j.toRingHom ≫ xS ≫ gS.left ≫ pullback.fst _ _ := by rw [reassoc_of% c1]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ c.left := by rw [hz, reassoc_of% eji]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ spMap ρ.toRingHom ≫ spMap i.toRingHom ≫ c.left := by
          rw [reassoc_of% eρi]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ xL ≫ bcMap A.hom ρ ≫ gS.left ≫ pullback.fst _ _ := by
          rw [reassoc_of% c3, hz]
        _ = y.left ≫ bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ := by
          rw [hg, reassoc_of% c2]
    · have e1 : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
      have e2 : h.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w h
      simp only [Over.comp_left, Category.assoc]
      rw [e1, e2]
  rw [← hhe, ← hfe, e]

theorem chow_rigidity : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A', IsMonHom f → ∃ g : (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A', IsMonHom g ∧ GlobalTheory.Spread.bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ := by
  intro K Ω _ _ _ _ _ A A' _ _ hA hA' f hf
  have := hA.proper; have := hA.smooth; have := hA'.proper; have := hA'.smooth
  have := hf
  obtain ⟨R, gR, ⟨s, hs⟩, hgR, hR⟩ := GlobalTheory.HomDescent.exists_fg_isMonHom f
  have := hgR
  haveI : IsAlgClosed (algebraicClosure K Ω) := IsAlgClosure.isAlgClosed K
  let S : Subalgebra (algebraicClosure K Ω) Ω := Algebra.adjoin (algebraicClosure K Ω) (s : Set Ω)
  haveI : Algebra.FiniteType (algebraicClosure K Ω) S := ⟨(Subalgebra.fg_top S).mpr ⟨s, rfl⟩⟩
  obtain ⟨ρ₀⟩ := GlobalTheory.Ex.ThetaDescent.nonempty_algHom (algebraicClosure K Ω) S
  have hRS : ∀ r ∈ R, r ∈ S := fun r hr => by
    have h1 : Algebra.adjoin K (s : Set Ω) ≤
        (Algebra.adjoin (algebraicClosure K Ω) (s : Set Ω)).restrictScalars K :=
      Algebra.adjoin_le Algebra.subset_adjoin
    rw [← hs] at hr
    exact h1 hr
  let inc : R →ₐ[K] S :=
    { toFun := fun r => ⟨r, hRS r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let i : algebraicClosure K Ω →ₐ[K] S := IsScalarTower.toAlgHom K (algebraicClosure K Ω) S
  let j : S →ₐ[K] Ω := S.val.restrictScalars K
  let ρ : S →ₐ[K] algebraicClosure K Ω := ρ₀.restrictScalars K
  obtain ⟨gS, hgS, hgSe⟩ := GlobalTheory.HomDescent.exists_specialise gR inc
  have := hgS
  obtain ⟨g, hg, hge⟩ := GlobalTheory.HomDescent.exists_specialise gS ρ
  have := hg
  refine ⟨g, hg, ?_⟩
  rw [compare K Ω S i j ρ Subtype.val_injective (fun _ => rfl) (fun x => ρ₀.commutes x) A A' hA hA' gS g hge,
    hgSe, ← hR, bcMap_comp_of_eq_assoc A.hom inc j R.val fun _ => rfl]

end GlobalTheory.ChowRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem nef_big_of_cls_eq_smul_add_smul : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (a b : ℕ), IsNef k N → IsBig k N → IsNef k N' → 0 < a → ∃ (N₀ : LB X) (h₀ : N₀.IsLB), cls N₀ h₀ = a • cls N hN + b • cls N' hN' ∧ IsNef k N₀ ∧ IsBig k N₀ := by
  intro hNN k _ X _ q hq
  letI := algebraΓOfHom q
  intro N N' hN hN' a b hNn hNb hN'n ha
  have hp : IsProjOver (strHom k (X := X)) := by
    rwa [strHom_eq (f := q) fun _ => rfl]
  obtain ⟨_, hH⟩ := exists_isAmpleLB_of_isProjOver hq
  refine ⟨tens (lbPow N a) (lbPow N' b), isLB_tens (isLB_lbPow hN a) (isLB_lbPow hN' b), ?_, ?_, ?_⟩
  · rw [cls_tens (isLB_lbPow hN a) (isLB_lbPow hN' b), cls_lbPow hN, cls_lbPow hN']
  · exact (hNn.pow hH a).tens (hN'n.pow hH b) hH
  · exact (hNb.pow (fun _ => rfl) hq ha).tens_nef hNN hp (hNn.pow hH a) (hN'n.pow hH b)

end GlobalTheory
end

