module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfGenericUniqueComplexPoint
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem exists_mul_eq_of_generic_unique_complexPoint : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG → B.FG → B ≤ A → (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) → ∀ a ∈ A, ∃ p ∈ B, ∃ q ∈ B, q ≠ 0 ∧ a * q = p := by
  intro K Ω _ _ _ σ A B hA hB hBA H a haA
  by_contra hne
  haveI : CharZero K := ⟨fun m n h => Nat.cast_injective (R := ℂ) (by simpa using congrArg σ h)⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L := IntermediateField.adjoin K (B : Set Ω)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have haL : a ∉ Set.range (algebraMap L Ω) := by
    rintro ⟨l, hl⟩
    have hmem : a ∈ L := hl ▸ l.2
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hmem
    rw [Algebra.adjoin_eq] at hr hs
    apply hne
    by_cases hs0 : s = 0
    · exact ⟨0, B.zero_mem, 1, B.one_mem, one_ne_zero, by simp [hs0]⟩
    · exact ⟨r, hr, s, hs, hs0, div_mul_cancel₀ r hs0⟩
  obtain ⟨F, _, i₁, i₂, hi, hne2⟩ := GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range L Ω a haL
  letI : Algebra B A := (Subalgebra.inclusion hBA).toRingHom.toAlgebra
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun k => rfl
  haveI : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).1 hA
  haveI : Algebra.FiniteType K B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType K B A
  let j₁ : A →+* F := i₁.comp A.val.toRingHom
  let j₂ : A →+* F := i₂.comp A.val.toRingHom
  have hBL : ∀ b : B, (b : Ω) = algebraMap L Ω ⟨b, IntermediateField.subset_adjoin K _ b.2⟩ := fun b => rfl
  have hj : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) := by
    ext b
    change i₁ (b : Ω) = i₂ (b : Ω)
    rw [hBL b]
    exact congrArg (fun f : L →+* F => f _) hi
  have hinj : Function.Injective (j₁.comp (algebraMap B A)) := by
    intro b c h
    exact Subtype.ext (i₁.injective h)
  obtain ⟨q, hq, Hq⟩ := GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' B A F j₁ j₂ hj hinj ⟨a, haA⟩ hne2
  obtain ⟨x, hxσ, hxq, hxu⟩ := H q q.2 (fun h => hq (Subtype.ext h))
  let φ : B →+* ℂ := x.comp (algebraMap B A)
  have hφq : φ q ≠ 0 := hxq (hBA q.2)
  obtain ⟨y₁, y₂, h₁, h₂, hy⟩ := Hq φ hφq
  have key : ∀ y : A →+* ℂ, y.comp (algebraMap B A) = φ → y = x := by
    intro y hy
    refine hxu y (fun k => ?_) (fun a' ha' => ?_)
    · have e1 : algebraMap K A k = algebraMap B A (algebraMap K B k) := rfl
      rw [e1, ← hxσ k, e1]
      exact congrArg (fun f : B →+* ℂ => f (algebraMap K B k)) hy
    · have e1 : a' = algebraMap B A ⟨a', ha'⟩ := rfl
      rw [e1]
      exact congrArg (fun f : B →+* ℂ => f ⟨a', ha'⟩) hy
  exact hy (by rw [key y₁ h₁, key y₂ h₂])

end GlobalTheory.DegVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihila
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolExists

theorem exists_sum_wedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (a b : Fin n → M), ∑ k, exteriorPower.ιMulti R 2 ![a k, b k] = w := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, a, b, rfl⟩ := hx
    obtain ⟨m, c, d, rfl⟩ := hy
    refine ⟨n + m, Fin.append a c, Fin.append b d, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r x _ hx =>
    obtain ⟨n, a, b, rfl⟩ := hx
    refine ⟨n, fun k ↦ r • a k, b, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • a k, b k] : Fin 2 → M) = Function.update ![a k, b k] 0 (r • ![a k, b k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

theorem mem_of_annihilates {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ψ : LinearMap.BilinForm K V) [hψ : ψ.IsPerfPair] (F : Submodule K V)
    (hiso : ∀ f ∈ F, ∀ g ∈ F, ψ f g = 0) (hdim : 2 * Module.finrank K F = Module.finrank K V) (f : V)
    (hf : ∀ g ∈ F, ψ f g = 0) : f ∈ F := by
  let Φ : V →ₗ[K] Module.Dual K F := F.subtype.dualMap ∘ₗ ψ
  have hΦ : Function.Surjective Φ :=
    (LinearMap.dualMap_surjective_of_injective F.injective_subtype).comp hψ.bijective_left.2
  have hker : F ≤ LinearMap.ker Φ := fun f hf' ↦ LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ hiso f hf' g g.2)
  have hr := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.2 hΦ, finrank_top, Subspace.dual_finrank_eq] at hr
  have heq : F = LinearMap.ker Φ := Submodule.eq_of_le_of_finrank_eq hker (by omega)
  rw [heq]
  exact LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ hf g g.2)

theorem isGen_self {X : Scheme.{0}} {L : Semi.LB X} (hL : L.IsLB) :
    Semi.LB.Gen.IsGen (⟨fun p => L.g p.1 p.2⟩ : Semi.LB.Iso L L) := by
  refine fun p q => unit_ext fun y hy => ?_
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

end GlobalTheory.PolExists

namespace GlobalTheory.PolExists

open GlobalTheory.Published GlobalTheory.CatCoh

theorem polForm_exists : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X}
    {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  intro P E _ _ _ H Dw l Xo K _ x A _ π hπ
  have hA : Semi.IsAbelianScheme A := by
    have hG := ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hc : IsCommMonObj A := by
      open MonoidalCategory CartesianMonoidalCategory MonObj in
      open scoped CategoryTheory.Obj in
        exact (by
          rw [isCommMonObj_iff_isMulCommutative]
          intro T
          refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
          rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
            ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm])
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 K A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso K ⊥ (dp0 K) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 K) (𝟙 _) A
    rw [show prim (dp0 K) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 K) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 K) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (isGen_self hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 K A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩

  obtain ⟨hfin, -, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, -, hFfin, -, hFrk⟩ := P.2.1 K A _ hA gA
  let p : PrimeSpectrum K := IsLocalRing.closedPoint K
  have d1 : Module.finrank K (primDR A) = 2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have d2 : Module.finrank K (PrimitiveSubmodule A) = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have := hFrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have d3 := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
  have d4 : Module.finrank K (HdR A) = Module.finrank K (primDR A) := Subspace.dual_finrank_eq
  exact mem_of_annihilates _ (Fil A) hiso (by
    change 2 * Module.finrank K (PrimitiveSubmodule A).dualAnnihilator = _
    omega) f hf

end GlobalTheory.PolExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.OActPull

theorem exists_oAct_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (b : OAct O G) {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hg : IsGrpPullback G' G f φ) : ∃ a : OAct O G', ∀ z, (a.act z).left ≫ φ = φ ≫ (b.act z).left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (φ ≫ (b.act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ φ = φ ≫ (b.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ b.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a c => inj ?_, fun a c => inj ?_⟩, ha⟩
  · have := b.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, b.one, Category.comp_id]
  · rw [← Category.id_comp (act (a * c)), pa, pa, ← Category.id_comp (act a), pa, b.mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act c)).symm
    rw [← Category.id_comp (act (a + c)), ← Category.id_comp (act a), ← Category.id_comp (act c), pa, pa, pa, b.add]
    exact MonObj.comp_mul _ _ _

end GlobalTheory.OActPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCanonTensPullId
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModifRefl

theorem exists_sec_canon_tens_pull_id : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D (𝟙 Y ≫ p)] (B : LB Y), B.IsLB → ∀ (s : H0 p (tens (CanonLB.all p D).bundle B) ⊤) (y : Y), y ∈ nonzeroLocus (toSec s) → ∃ s' : H0 (𝟙 Y ≫ p) (tens (CanonLB.all (𝟙 Y ≫ p) D).bundle (B.pull (𝟙 Y))) ⊤, y ∈ nonzeroLocus (toSec s') := by
  intro k _ Y p D _ inst2 B hB s y hy
  revert inst2
  generalize hq : 𝟙 Y ≫ p = q
  simp only [Category.id_comp] at hq
  subst hq
  intro inst2
  have hK : (CanonLB.all p D).bundle.IsLB := (CanonLB.all p D).isLB
  have hBp : (B.pull (𝟙 Y)).IsLB := LB.isLB_linComb hB _ _
  have H1 : LBIso (tens (B.pull (𝟙 Y)) (CanonLB.all p D).bundle) (tens B (CanonLB.all p D).bundle) :=
    GlobalTheory.CechPic.tens_congr_left hK (DescendedPrincipal.lbIso_pull_id hB)
  have H : LBIso (tens (CanonLB.all p D).bundle (B.pull (𝟙 Y))) (tens (CanonLB.all p D).bundle B) :=
    LBIso.trans (isLB_tens hK hBp) (isLB_tens hBp hK) (isLB_tens hK hB)
      (GlobalTheory.CechPic.tens_comm_iso hK hBp)
      (LBIso.trans (isLB_tens hBp hK) (isLB_tens hB hK) (isLB_tens hK hB) H1
        (GlobalTheory.CechPic.tens_comm_iso hB hK))
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_tens hK hBp) (isLB_tens hK hB) H (toSec s)
  refine ⟨H0.ofSec p ⊤ t, ?_⟩
  have e : toSec (H0.ofSec p ⊤ t) = t := by
    unfold toSec
    exact Equiv.ofBijective_symm_apply_apply _ _ _
  rw [e, ht]
  exact hy

end GlobalTheory.ModifRefl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtensionOfDenseLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem eq_zero_of_ger_dense {Y : Scheme.{0}} [IsReduced Y] {O V : Y.Opens} (hd : Dense (O : Set Y))
    (a : Γ(Y, V)) (h : ∀ z (hz : z ∈ V), z ∈ O → ger z hz a = 0) : a = 0 := by
  refine eq_zero_of_basicOpen_eq_bot a ?_
  by_contra hne
  obtain ⟨y, hy', hy⟩ := hd.inter_open_nonempty _ (Y.basicOpen a).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have hm := Y.basicOpen_le _ hy'
  have hu : IsUnit (ger y hm a) := (Y.mem_basicOpen _ y hm).1 hy'
  rw [h y hm hy] at hu
  exact not_isUnit_zero hu

theorem exists_ext_of_dense_local : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} [IsReduced Y] (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (O : Y.Opens), Dense (O : Set Y) → ∀ (m : H0 p B O), (∀ y : Y, y ∉ O → ∃ (W : Y.Opens) (i : B.ι) (hi : W ≤ B.U i) (b : Γ(Y, W)), y ∈ W ∧ (∀ y' (h : y' ∈ W) (h' : y' ∈ O), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∉ O → ger y' h b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y')) → ∃ s : H0 p B ⊤, H0.restr le_top s = m ∧ ∀ y : Y, y ∉ O → ∀ (i : B.ι) (hi : y ∈ B.U i), H0.germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  intro k _ Y _ p B hB O hd m hloc
  choose W i hi b hyW hagree hmax using hloc
  let τ := B.ι ⊕ {y : Y // y ∉ O}
  let V : τ → Y.Opens := fun t => Sum.elim (fun j => O ⊓ B.U j) (fun y => W y.1 y.2) t
  let c : τ → B.ι := fun t => Sum.elim (fun j => j) (fun y => i y.1 y.2) t
  have hc : ∀ t, V t ≤ B.U (c t) := fun t => by
    rcases t with j | ⟨y, hy⟩
    · exact inf_le_right
    · exact hi y hy
  let u : ∀ t, Γ(Y, V t) := fun t => match t with
    | Sum.inl j => m.loc j
    | Sum.inr y => b y.1 y.2
  have key : ∀ t z (h : z ∈ V t) (hz : z ∈ O), ger z h (u t) = H0.germ (c t) z hz (hc t h) m := by
    intro t z h hz
    rcases t with j | ⟨y, hy⟩
    · rfl
    · exact hagree y hy z h hz
  have cover : ∀ y ∈ (⊤ : Y.Opens), ∃ t, y ∈ V t := fun y _ => by
    by_cases hy : y ∈ O
    · obtain ⟨j, hj⟩ := exists_chart hB y
      exact ⟨Sum.inl j, hy, hj⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, hyW y hy⟩
  have rule : ∀ y t t' (h : y ∈ V t) (h' : y ∈ V t'),
      ger y h (u t) = tr B y (c t) (c t') * ger y h' (u t') := by
    intro y t t' h h'
    have l₁ : V t ⊓ V t' ≤ V t := inf_le_left
    have l₂ : V t ⊓ V t' ≤ V t' := inf_le_right
    have l₃ : V t ⊓ V t' ≤ B.U (c t) ⊓ B.U (c t') := inf_le_inf (hc t) (hc t')
    have hz : ∀ z (hz : z ∈ V t ⊓ V t'), ger z hz (resG Y l₁ (u t) -
        resG Y l₃ (B.g (c t) (c t')).val * resG Y l₂ (u t')) =
        ger z (l₁ hz) (u t) - (tr B z (c t) (c t')).val * ger z (l₂ hz) (u t') := by
      intro z hz
      rw [map_sub, map_mul, ger_resG, ger_resG, ger_resG, val_tr B z (l₃ hz)]
    have e := eq_zero_of_ger_dense hd _ fun z hzV hzO => by
      rw [hz z hzV, key t z (l₁ hzV) hzO, key t' z (l₂ hzV) hzO, sub_eq_zero]
      exact H0.germ_change _ _ z hzO _ _ m
    have e' := congrArg (ger y (memInf h h')) e
    rw [hz y (memInf h h'), map_zero, sub_eq_zero] at e'
    exact e'
  obtain ⟨f, hf⟩ := H0.exists_of_germs (p := p) (O := ⊤) hB V c (fun _ => le_top) hc cover u rule
  refine ⟨f, ?_, ?_⟩
  · refine H0.ext_germ fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart hB y
    refine ⟨j, hj, ?_⟩
    rw [H0.germ_restr]
    exact (hf (Sum.inl j) y ⟨hy, hj⟩).trans rfl
  · intro y hy j hj
    rw [H0.germ_change j (i y hy) y _ hj (hi y hy (hyW y hy))]
    have e := hf (Sum.inr ⟨y, hy⟩) y (hyW y hy)
    refine (congrArg (fun x => (tr B y j (i y hy)).val * x) e).symm ▸ ?_
    exact Ideal.mul_mem_left _ _ (hmax y hy y (hyW y hy) hy)

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAffineChartBoundaryZeroSet
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

namespace GlobalTheory.CompHS.ChartBd

theorem mem_iff_not_mem_basicOpen {X : Scheme.{0}} (C : Closeds X) (U : X.affineOpens) (g : Γ(X, U.1))
    (hD : (Scheme.IdealSheafData.vanishingIdeal C).ideal U = Ideal.span {g}) (x : X) (hx : x ∈ U.1) :
    x ∈ C ↔ x ∉ X.basicOpen g := by
  obtain ⟨s, rfl⟩ : x ∈ Set.range U.2.fromSpec := by rw [U.2.range_fromSpec]; exact hx
  have hcl : IsClosed (U.2.fromSpec ⁻¹' (C : Set X)) := C.isClosed.preimage U.2.fromSpec.continuous
  have hz : PrimeSpectrum.zeroLocus ((Scheme.IdealSheafData.vanishingIdeal C).ideal U : Set Γ(X, U.1)) =
      U.2.fromSpec ⁻¹' (C : Set X) := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hcl.closure_eq
  have h1 : U.2.fromSpec s ∈ X.basicOpen g ↔ s ∈ PrimeSpectrum.basicOpen g := by
    rw [← U.2.fromSpec_preimage_basicOpen]; rfl
  have h2 : U.2.fromSpec s ∈ C ↔ s ∈ U.2.fromSpec ⁻¹' (C : Set X) := Iff.rfl
  have h3 : s ∈ PrimeSpectrum.basicOpen g ↔ g ∉ (s : PrimeSpectrum Γ(X, U.1)).asIdeal :=
    PrimeSpectrum.mem_basicOpen g s
  have h4 : s ∈ U.2.fromSpec ⁻¹' (C : Set X) ↔ g ∈ (s : PrimeSpectrum Γ(X, U.1)).asIdeal := by
    rw [← hz, hD, PrimeSpectrum.zeroLocus_span]
    exact (PrimeSpectrum.mem_zeroLocus (s : PrimeSpectrum Γ(X, U.1)) {g}).trans Set.singleton_subset_iff
  exact h2.trans (h4.trans (not_not.symm.trans (h1.trans h3).not.symm))

end GlobalTheory.CompHS.ChartBd

namespace GlobalTheory.CompHS.ChartBd

theorem exists_chart_bd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw), IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, ∃ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (p : Γ(Y₀ TF.X Z, W)), y ∈ W ∧ W ≤ (L₀ TF.X Z la).U i ∧ IsDomain Γ(Y₀ TF.X Z, W) ∧ RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)).hom ∧ p ≠ 0 ∧ ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
  intro E _ _ _ H Dw l Xo c TF Z la hV y

  let q : Y₀ TF.X Z ⟶ TF.Y.X := inc₀ TF.X Z ≫ TF.X.π
  obtain ⟨-, U', hxU', n, f, J, -, hD⟩ := TF.snc (q y)
  let g : Γ(TF.Y.X, U'.1) := ∏ i ∈ J, f i
  have hZ : ∀ x ∈ U'.1, x ∈ (LogKS.interior TF.Y).compl ↔ x ∉ TF.Y.X.basicOpen g :=
    mem_iff_not_mem_basicOpen _ U' g hD

  have hs : Smooth (str₀ TF.X Z) := by
    haveI := hV.1
    exact SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) (str₀ TF.X Z)
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ _ hs
  have := GlobalTheory.IsNormalScheme.of_pred hn
  obtain ⟨W₁, hyW₁, hW₁⟩ := GlobalTheory.ModelChart.exists_open_isDomain (Y₀ TF.X Z) y
  obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ TF.X Z la) y
  let O : (Y₀ TF.X Z).Opens := W₁ ⊓ (L₀ TF.X Z la).U i ⊓ q ⁻¹ᵁ U'.1
  have hyO : y ∈ O := ⟨⟨hyW₁, hi⟩, hxU'⟩
  obtain ⟨W, hW, hyW, hWO⟩ := exists_isAffineOpen_mem_and_subset (U := O) (x := y) hyO
  have hWO' : W ≤ O := hWO
  have hWq : W ≤ q ⁻¹ᵁ U'.1 := hWO'.trans inf_le_right
  let p : Γ(Y₀ TF.X Z, W) := (Y₀ TF.X Z).presheaf.map (homOfLE hWq).op (q.app U'.1 g)
  have hbo : (Y₀ TF.X Z).basicOpen p = W ⊓ q ⁻¹ᵁ TF.Y.X.basicOpen g := by
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  have key : ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
    intro y' hy'
    have e1 : y' ∈ bd₀ TF.X Z ↔ q y' ∈ (LogKS.interior TF.Y).compl := Iff.rfl
    have e2 : y' ∈ (Y₀ TF.X Z).basicOpen p ↔ q y' ∈ TF.Y.X.basicOpen g := by
      rw [hbo]; exact ⟨fun h => h.2, fun h => ⟨hy', h⟩⟩
    rw [e1, e2]
    exact hZ _ (hWq hy')
  refine ⟨W, hW, i, p, hyW, hWO'.trans (inf_le_left.trans inf_le_right), hW₁ W hyW (hWO'.trans (inf_le_left.trans inf_le_left)), ?_, ?_, key⟩
  · have hφ : Spec.map (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)) =
        (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z := Spec.map_preimage _
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp (by rw [hφ]; infer_instance)
  · intro hp0
    obtain ⟨y', hy'W, hy'U⟩ := (dense_U₀ TF.X Z).inter_open_nonempty W W.isOpen ⟨y, hyW⟩
    have h := (key y' hy'W).not.mp (not_not.mpr hy'U)
    rw [hp0, Scheme.basicOpen_zero] at h
    exact h (by simp)

end GlobalTheory.CompHS.ChartBd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentFunctionFieldFg
section
set_option autoImplicit false

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem om_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (Om Z)).FG := by
  intro E _ _ _ H Dw l Xo c r U _ Z
  exact fnFG_of Xo c (kapFG_pf Xo c) Z

end GlobalTheory.DegVal
end

