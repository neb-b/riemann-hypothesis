module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem hasDiv_of_pCrd_pt : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω)
    (n : ℕ) (g : M.Z ⟶ PSpace o n) (e : Fin (n + 1) → Ω), PCrd (M.pt ≫ g) e → M.HasDiv e := by
  intro k Ω o _ _ _ _ M n g e hP z
  obtain ⟨τ, -, H⟩ := hP
  obtain ⟨c, hc⟩ := GlobalTheory.ProjSpace.exists_mem_chart o n (g z)
  let W : M.Z.Opens := g ⁻¹ᵁ GlobalTheory.ProjSpace.chart o n c
  have hzW : z ∈ W := hc
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ W := M.top_le_preimage_pt ⟨z, hzW⟩
  let j : PUnit → (GlobalTheory.ProjSpace.O1 o n).ι := fun _ => c
  let V := ((GlobalTheory.ProjSpace.O1 o n).pull (M.pt ≫ g)).U j
  have hV : V ≤ (M.pt ≫ g) ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o n).U (j PUnit.unit) :=
    LB.wchart_le (GlobalTheory.ProjSpace.O1 o n) (fun _ => M.pt ≫ g) j PUnit.unit
  have hV' : ⊤ ≤ V := fun y _ => Set.mem_iInter.2 fun _ => hW (Set.mem_univ y)
  let ev : Γ(Sp Ω, V) →+* Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp ((Sp Ω).presheaf.map (homOfLE hV').op).hom
  have hconst : ∀ a : Ω, ev (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a := by
    intro a
    change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (((Sp Ω).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      (Sp Ω).presheaf.map (homOfLE hV').op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a
    rw [← Functor.map_comp]
    have : ((homOfLE (le_top : V ≤ ⊤)).op ≫ (homOfLE hV').op : Opposite.op (⊤ : (Sp Ω).Opens) ⟶ _) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    exact (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv_hom_id_apply a
  have hval : ∀ i, ev (((M.pt ≫ g).appLE _ _ hV).hom ((GlobalTheory.ProjSpace.coord o n i).f (j PUnit.unit))) =
      valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) := by
    intro i
    rw [valF, dite_eq_left hW]
    change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (resG (Sp Ω) hV' _) = _
    rw [GlobalTheory.ProjSpace.resG_appLE, GlobalTheory.ProjSpace.pullRatio, GlobalTheory.ProjSpace.appLE_appLE]
    rfl
  have key : ∀ i, valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) = e i * ev (τ.s j).val := by
    intro i
    rw [← hval, H i j hV, map_mul, hconst]
  have h1 : e c * ev (τ.s j).val = 1 := by
    rw [← key c, GlobalTheory.ProjSpace.pullRatio_self, ← M.res_apply W ⟨z, hzW⟩, map_one]
  have hc0 : e c ≠ 0 := left_ne_zero_of_mul_eq_one h1
  refine ⟨c, hc0, fun i => ?_⟩
  have e1 : e i / e c = valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) := by
    rw [key i, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]
  rw [e1]
  exact RatModel.valF_mem_O hzW _

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSemiAbelianRelDimCotangentVectorBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelRelDim

theorem relDim_and_isVB_omega : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom ∧ GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l Xo c Y
  have := Y.t.semi
  have hsm : Smooth Y.t.G.hom := Y.t.semi.smooth
  have : IsIso (spMap (RingHom.id c.F)) := by
    unfold spMap
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  have hdom : IsDominant (Y.jQ ≫ pullback.fst Y.s (spMap (RingHom.id c.F))) := inferInstance
  have hg : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom :=
    GlobalTheory.smoothOfRelativeDimension_of_isPullback_isDominant _ _ _ _ _ Y.t.G.hom Y.oF.t.G.hom Y.m.φ _
      Y.m.cart.1 hdom hsm (GlobalTheory.ObjDim.smoothOfRelativeDimension Y.oF)
  exact ⟨hg, GlobalTheory.LieVB.isVB_omega Y.t.G _⟩

end GlobalTheory.ModelRelDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelValueAtPointOfOpenViaSpecSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_eq_of_spMap : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (Rs : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp Rs), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap Rs.val.toRingHom) → ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : Rs →+* K), spMap f = q ≫ u₀ → ∀ a : Rs, M.val (q ≫ U₀.ι) (a : Ω) = f a := by
  intro o Ω _ _ _ M U₀ Rs u₀ hne hpt K _ q f hf a
  set s : Γ(U₀.toScheme, ⊤) :=
    (u₀.appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of Rs)).inv.hom a) with hs
  set t : Γ(M.Z, U₀.ι ''ᵁ ⊤) := (U₀.ι.appIso ⊤).inv.hom s with ht
  have key : ∀ {C : Type} [Field C] (y : Sp C ⟶ U₀.toScheme),
      valF (y ≫ U₀.ι) (U₀.ι ''ᵁ ⊤) t = valR (y ≫ u₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Rs)).inv.hom a) := by
    intro C _ y
    rw [GlobalTheory.Points.valF_eq_valR, ← GlobalTheory.Points.valR_appLE y U₀.ι (U₀.ι.preimage_image_eq ⊤).ge
      (GlobalTheory.Points.le_preimage_top y), ← Scheme.Hom.appIso_hom', ht, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply, hs]
    exact GlobalTheory.Points.valR_appLE y u₀ _ (GlobalTheory.Points.le_preimage_top y) _
  have hW : ∀ {C : Type} [Field C] (y : Sp C ⟶ U₀.toScheme),
      Set.range (y ≫ U₀.ι) ⊆ ((U₀.ι ''ᵁ ⊤ : M.Z.Opens) : Set M.Z) := by
    intro C _ y
    rw [Scheme.Opens.ι_image_top, ← Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ⟨y w, rfl⟩
  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact M.top_le_preimage_pt hne (x := w) trivial
  have hx : IsOpenImmersion.lift U₀.ι M.pt hrange ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have h1 := hpt _ hx
  have e1 : valF M.pt (U₀.ι ''ᵁ ⊤) t = (a : Ω) := by
    rw [← hx, key, h1, GlobalTheory.Points.valR_specMap]
    rfl
  rw [RatModel.val_eq (hW q) e1, key, ← hf, GlobalTheory.Points.valR_specMap]
  rfl

end GlobalTheory.Poinc.TestAtPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliGeometricPointEqOfSameFibreActionLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem moduli_point_eq_of_same_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (x x' : Sp K ⟶ Xo.X) (α α' : P.A.left ⟶ Xo.univ.t.G.left), x ≫ Xo.s = x' ≫ Xo.s → IsGrpPullback P.A Xo.univ.t.G x α → IsGrpPullback P.A Xo.univ.t.G x' α' → LBIso P.L (Xo.univ.t.PP.L.pull α) → LBIso P.L (Xo.univ.t.PP.L.pull α') → (∀ a, ∃ h : P.A ⟶ P.A, h.left ≫ α = α ≫ (Xo.univ.t.act.act a).left ∧ h.left ≫ α' = α' ≫ (Xo.univ.t.act.act a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.eta a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.eta a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.etaA a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.etaA a).left) → x = x' := by
  intro E _ _ _ H D l Xo K _ _ P x x' α α' hs hα hα' hL hL' hact hM hA
  choose act h₁ h₂ using hact
  have h : GlobalTheory.ArcUnique.IsFibre P.A act P.L Xo.univ.t x α := ⟨hα, h₁, hL⟩
  have h' : GlobalTheory.ArcUnique.IsFibre P.A act P.L Xo.univ.t x' α' := ⟨hα', h₂, hL'⟩
  obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ (Sp K) Xo.s
    (x ≫ Xo.s) x rfl rfl ((Category.comp_id _).symm.trans (congrArg ((x ≫ Xo.s) ≫ ·) (Spec.map_id _).symm)) Xo.univ
  obtain ⟨ρ, e₁, g, ha, hi⟩ := h.cancel P.isLB o'.t.PP.isLB (GlobalTheory.ArcUnique.isFibre_of_sabMap m.toSABMap)
    (Category.id_comp x)
  obtain ⟨f₁, f₂, f₃⟩ := h'.precomp P.isLB o'.t.PP.isLB g ha hi
  rw [Category.id_comp] at f₁
  have := o'.proper
  obtain ⟨m', hm'⟩ := exists_sabMap_of_lbIso E H _ _ Xo.univ.t o'.t x' (ρ ≫ α')
    ⟨inferInstance, fun s _ K _ _ t _ => inferInstance⟩ f₁ f₂ f₃
  have key : ∀ (y : 𝟙_ (Over (Sp K)) ⟶ o'.t.G) (w : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
      y.left ≫ m.toSABMap.φ = x ≫ w.left →
      (∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ w.left ∧ z.left ≫ α' = x' ≫ w.left) →
      y.left ≫ m'.φ = x' ≫ w.left := by
    rintro y w hy ⟨z, z₁, z₂⟩
    have e : y.left ≫ ρ = z.left := hα.1.hom_ext (by rw [Category.assoc, e₁, hy, z₁]) (by
      rw [Category.assoc, g.1.w, ← Category.assoc, Over.w, Over.w]
      exact Category.comp_id _)
    rw [hm', ← Category.assoc, e, z₂]
  exact (Xo.rep _ _ inferInstance o').unique ⟨rfl, ⟨m⟩⟩
    ⟨hs.symm, ⟨⟨m', fun a => key _ _ (m.eta a) (hM a), fun a => key _ _ (m.etaA a) (hA a)⟩⟩⟩

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeCoefficientFieldNormalNoetherianSepa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem xF_charZero_residueField {X : Scheme.{0}} {K : Type} [Field K] [CharZero K] (s : X ⟶ Sp K) (x : X) :
    CharZero (X.residueField x) := by
  let φ : K →+* X.residueField x :=
    (X.residue x).hom.comp ((X.presheaf.germ ⊤ x trivial).hom.comp
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
  exact (RingHom.charZero_iff φ.injective).1 inferInstance

theorem xF_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) , Geo.Tor.IsNormalScheme (Xo.XF c) ∧ IsLocallyNoetherian (Xo.XF c) ∧ (∀ x : Xo.XF c, CharZero ((Xo.XF c).residueField x)) ∧ IsSeparated (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ LocallyOfFiniteType (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ QuasiCompact (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨N, i, hi, hq, hc⟩ := Xo.qproj
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have : IsProper (PSpace.str (KA l) N) := isProper_str (KA l) N
  have : IsSeparated Xo.s := by rw [← hc]; infer_instance
  have : QuasiCompact Xo.s := by rw [← hc]; infer_instance
  have hsm : Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  obtain ⟨-, hn, hl⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm
  exact ⟨hn, hl, fun x => xF_charZero_residueField (pullback.snd _ _) x, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaSpreadStableSummandLieDecompositionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moritaSpread_stableSummand_lieDecomposition : ∀ {C : Type} [CommRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  (m : ℕ) [NeZero m] (E : Fin m → Fin m → Module.End C H),
  (∀ i j k l, E i j * E k l = if j = k then E i l else 0) → ∑ i, E i i = 1 →
  ∀ {A : Type} [CommRing A] (σ : A →+* Module.End C H), (∀ i j c, E i j * σ c = σ c * E i j) →
  ∀ {O : Type} [Ring O] (ρ : O →+* Module.End C H),
  (∀ (c : O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x → E 0 i (ρ c (E j 0 x)) ∈ N) →
  ∀ (e : Module.End C H), e * e = e → (∀ i j, E i j * e = e * E i j) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ i j, ∀ x ∈ F, E i j x ∈ F) → (∀ x ∈ F, e x ∈ F) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (G₀ M₀ : Submodule C H), G₀ ⊓ M₀ = ⊥ → G₀ ⊔ M₀ = LinearMap.range (E 0 0 * e) →
    (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) → G₀ ⊔ I • LinearMap.range (E 0 0 * e) = F ⊓ LinearMap.range (E 0 0 * e) →
    (∀ d ∈ LinearMap.range (E 0 0 * e), ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀) →
  ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : O), ∀ x ∈ G, ρ c x ∈ G) ∧
    G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧
    ∀ d ∈ LinearMap.range e, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  first | (exact @GlobalTheory.morita_spread_stable_summand_lie) | (exact GlobalTheory.morita_spread_stable_summand_lie) | (intros; apply GlobalTheory.morita_spread_stable_summand_lie  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfMulAtDominantPairCommGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mul_of_isDominant_pair : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], GlobalTheory.SS.SmConn A → ∀ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left → ∀ (Y : Over (Sp K)) (x₁ x₂ y₁ y₂ : Y ⟶ A), IsDominant (lift x₁ x₂).left → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₁ → u ≫ f = w ≫ y₁) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₂ → u ≫ f = w ≫ y₂) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ (x₁ * x₂) → u ≫ f = w ≫ (y₁ * y₂)) → ∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f := by
  intro K _ A _ hA V j f hj Y x₁ x₂ y₁ y₂ hdom h₁ h₂ h₃ Z u₁ u₂ u₃ hu
  obtain ⟨_, hsm, hsep, _, _⟩ := hA
  let R : A.left.Opens := j.left.opensRange
  let U : (A ⊗ A).left.Opens :=
    (fst A A).left ⁻¹ᵁ R ⊓ (snd A A).left ⁻¹ᵁ R ⊓ (fst A A * snd A A).left ⁻¹ᵁ R
  let W : Over (Sp K) := Over.mk (U.ι ≫ (A ⊗ A).hom)
  let ιW : W ⟶ A ⊗ A := Over.homMk U.ι rfl
  have : IsOpenImmersion ιW.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hWU : ∀ q : W.left, ιW.left q ∈ U := fun q => (Scheme.Opens.range_ι U).subset ⟨q, rfl⟩
  have hR : ∀ (g : A ⊗ A ⟶ A) (q : W.left), ιW.left q ∈ g.left ⁻¹ᵁ R →
      (ιW ≫ g).left q ∈ Set.range j.left := fun g q h => by
    rw [Over.comp_left, Scheme.Hom.comp_apply]; exact h
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ fst A A) fun q => hR _ q (hWU q).1.1
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ snd A A) fun q => hR _ q (hWU q).1.2
  obtain ⟨v₃, hv₃⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ (fst A A * snd A A)) fun q => hR _ q (hWU q).2
  have : Smooth (A ⊗ A).hom := inferInstanceAs (Smooth (pullback.fst A.hom A.hom ≫ A.hom))
  have : Smooth W.hom := inferInstanceAs (Smooth (U.ι ≫ (A ⊗ A).hom))
  have := GlobalTheory.isNormalScheme_of_smooth (S := Spec (.of K)) W.hom
  have : IsReduced W.left := GlobalTheory.IsNormalScheme.isReduced
  let Y' : Y.left.Opens := (lift x₁ x₂).left ⁻¹ᵁ U
  let Z' : Over (Sp K) := Over.mk (Y'.ι ≫ Y.hom)
  let w : Z' ⟶ Y := Over.homMk Y'.ι rfl
  let p : Z' ⟶ W := Over.homMk ((lift x₁ x₂).left ∣_ U) (by
    show (lift x₁ x₂).left ∣_ U ≫ U.ι ≫ (A ⊗ A).hom = Y'.ι ≫ Y.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])
  have hpw : p ≫ ιW = w ≫ lift x₁ x₂ := Over.OverMorphism.ext (morphismRestrict_ι _ _)
  have : IsDominant p.left := IsZariskiLocalAtTarget.restrict hdom U
  have e₁ : p ≫ v₁ ≫ f = w ≫ y₁ :=
    h₁ Z' w (p ≫ v₁) (by rw [Category.assoc, hv₁, ← Category.assoc, hpw, Category.assoc, lift_fst])
  have e₂ : p ≫ v₂ ≫ f = w ≫ y₂ :=
    h₂ Z' w (p ≫ v₂) (by rw [Category.assoc, hv₂, ← Category.assoc, hpw, Category.assoc, lift_snd])
  have e₃ : p ≫ v₃ ≫ f = w ≫ (y₁ * y₂) :=
    h₃ Z' w (p ≫ v₃) (by
      rw [Category.assoc, hv₃, ← Category.assoc, hpw, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd])
  have key : (v₁ ≫ f) * (v₂ ≫ f) = v₃ ≫ f := by
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated A.hom ?_ p.left ?_)
    · rw [Over.w, Over.w]
    · have : p ≫ ((v₁ ≫ f) * (v₂ ≫ f)) = p ≫ (v₃ ≫ f) := by
        rw [MonObj.comp_mul, e₁, e₂, e₃, MonObj.comp_mul]
      exact congrArg CommaMorphism.left this
  have hU : ∀ q : Z.left, (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ Set.range ιW.left := by
    intro q
    show _ ∈ Set.range U.ι
    rw [Scheme.Opens.range_ι]
    have hq : ∀ (g : A ⊗ A ⟶ A) (u : Z ⟶ V), lift (u₁ ≫ j) (u₂ ≫ j) ≫ g = u ≫ j →
        (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ g.left ⁻¹ᵁ R := fun g u e => by
      show g.left ((lift (u₁ ≫ j) (u₂ ≫ j)).left q) ∈ Set.range j.left
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
      exact ⟨u.left q, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩
    exact ⟨⟨hq _ u₁ (lift_fst _ _), hq _ u₂ (lift_snd _ _)⟩,
      hq _ u₃ (by rw [MonObj.comp_mul, lift_fst, lift_snd, hu])⟩
  obtain ⟨g, hg⟩ := GlobalTheory.GenericHom.exists_lift ιW (lift (u₁ ≫ j) (u₂ ≫ j)) hU
  have canc : ∀ a b : Z ⟶ V, a ≫ j = b ≫ j → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_mono j.left).1 (congrArg CommaMorphism.left e))
  have c₁ : g ≫ v₁ = u₁ := canc _ _ (by rw [Category.assoc, hv₁, ← Category.assoc, hg, lift_fst])
  have c₂ : g ≫ v₂ = u₂ := canc _ _ (by rw [Category.assoc, hv₂, ← Category.assoc, hg, lift_snd])
  have c₃ : g ≫ v₃ = u₃ := canc _ _ (by
    rw [Category.assoc, hv₃, ← Category.assoc, hg, MonObj.comp_mul, lift_fst, lift_snd, hu])
  rw [← c₁, ← c₂, ← c₃, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, key]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackFamilyNeZeroOdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mulFam_exists_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G → (∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0 := by
  intro R _ _ _ _ D m hm F₁ G hG ⟨α, j, hj⟩
  by_contra hcon
  push_neg at hcon
  apply hj
  have hfinite : IsFinite (mulA D.toPre.P.A m).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ D.toPre.P m hm.pos
  have hc := D.toPre.P.isAb.comm
  have hsm := D.toPre.P.isAb.smooth
  have hmhom := GlobalTheory.AbLaw.MulN.isMonHom_mulA D.toPre.P.A m
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ _),
      Flat ((Over.pullback t).map (mulA D.toPre.P.A m)).left ∧
        Surjective ((Over.pullback t).map (mulA D.toPre.P.A m)).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (TLinPf.isAb_pullback t D.toPre.P.A D.toPre.P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hfinite)
  have h₂ : Flat (mulA D.toPre.P.A m).left :=
    GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ _ _ _ inferInstance inferInstance
      inferInstance hfinite fun K _ _ t => (hgeo K t).1
  have h₃ : Surjective (mulA D.toPre.P.A m).left :=
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2
  obtain ⟨u, -, -, e⟩ := hG.1 α
  refine GlobalTheory.PullLin.sec_eq_zero_of_flat D.toPre.P.isLB (F₁.f α) (mulA D.toPre.P.A m).left (fun x J hJ => ?_) j
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (𝟙 _) x J hJ
  rw [ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius.sval_zero _ (hcon _), Category.id_comp] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackTraitGenericCondition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem gs_scal_over_self {W : Type} [CommRing W] {X Z : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of W)) (g : X ⟶ X)
    (hg : g ≫ q = q) (p : Z ⟶ X) (z : Z) (a : W) :
    gs (p ≫ g) z ⊤ (scal q a) = gs p z ⊤ (scal q a) := by
  have e : (g.app ⊤).hom (scal q a) = scal q a := by
    have e' : scal (g ≫ q) a = (g.app ⊤).hom (scal q a) := rfl
    rw [← e', hg]
  exact (gs_pull p g z ⊤ trivial (scal q a)).symm.trans (congrArg (gs p z ⊤) e)

theorem pullMul_trait_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ) (a : W)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ₀ (p ≫ (mulA C.A.A m).left) z J) →
    ∀ (σ : SecK C.P.L.L T.β 1) (σ₂ : SecK C.P.L.L T.β (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval θ₀ p' z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ₂ p z J = gs p z ⊤ (scal T.G.hom a) * sval S p' z J := by
  intro R _ _ _ D C W _ _ _ T m a u θ₀ S hS σ σ₂ hσ hσ₂ Z p p' hp z J hJ
  have e1 := GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m
  have e2 := GlobalTheory.ZH.TorsFrame.mulA_comm C.α_cart m
  have h : (p ≫ (mulA T.G m).left) ≫ T.β = (p' ≫ (mulA C.A.A m).left) ≫ C.α := by
    rw [Category.assoc, Category.assoc, e1, e2, ← Category.assoc, hp, Category.assoc]
  rw [hσ₂ Z p z J hJ, hσ Z _ _ h z J hJ, hS Z p' z J hJ, hp,
    gs_scal_over_self T.G.hom _ (Over.w (mulA T.G m)) p z a]
  exact mul_left_comm _ _ _

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordPairingRetractBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum


open GlobalTheory.HalfBC GlobalTheory.PullLinear GlobalTheory.FactorPull in
theorem lamRetract_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (inc : G ⟶ G₀) (v : G₀ ⟶ G₀) (L : LB G₀.left) (L₁ : LB ((Over.pullback f).obj G₀).left) (P : LB (G2 G).left), L.IsLB → L₁.IsLB → P.IsLB → LBIso L₁ (L.pull (pullback.fst G₀.hom f)) → LBIso P ((abelian₂ G₀ L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ v) : G2 G ⟶ G2 G₀).left) → ∃ π₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left, IsSquare (G' := (Over.pullback f).obj G) (G := G) (pullback.fst G.hom f) π₂ ∧ LBIso ((abelian₂ ((Over.pullback f).obj G₀) L₁).pull (lift (fst _ _ ≫ (Over.pullback f).map inc) (snd _ _ ≫ (Over.pullback f).map inc ≫ (Over.pullback f).map v) : G2 ((Over.pullback f).obj G) ⟶ G2 ((Over.pullback f).obj G₀)).left) (P.pull π₂) := by
  intro S S' f G _ _ G₀ _ _ inc v L L₁ P hL hL₁ hP hw hPw
  have gG := isGrpPullback_pullback G f
  have gG' := isGrpPullback_pullback G₀ f
  obtain ⟨wL, hwL⟩ := hw
  refine ⟨sqOf gG, isSquare_sqOf gG, ?_⟩
  have hm := lift_sq gG gG' (u := inc) (v := inc ≫ v) (u₁ := (Over.pullback f).map inc)
    (v₁ := (Over.pullback f).map inc ≫ (Over.pullback f).map v) (map_left_fst _ _)
    (by rw [← CategoryTheory.Functor.map_comp]; exact map_left_fst _ _)
  have H : LBIso _ _ := ⟨lamIso gG' wL, isGen_lamIso gG' wL hwL⟩
  have lL : (abelian₂ G₀ L).IsLB := DVR.linComb_isLB _ hL _ _
  have lL₁ : (abelian₂ _ L₁).IsLB := DVR.linComb_isLB _ hL₁ _ _
  have H₁ := H.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
    (chartPullLinComb (abelian₂ G₀ L) _ (fun _ => sqOf gG) (fun _ => sqOf gG') _ _ fun _ => hm.symm)
  have H₂ := hPw.chartPull (Geo.Tor.chartPullPull _ (sqOf gG) _ rfl) (Geo.Tor.chartPullPull _ (sqOf gG) _ rfl)
  exact LBIso.trans (pull_isLB lL₁ _) (pull_isLB (pull_isLB lL _) _) (pull_isLB hP _) H₁ H₂.symm

end GlobalTheory.Mum
end

