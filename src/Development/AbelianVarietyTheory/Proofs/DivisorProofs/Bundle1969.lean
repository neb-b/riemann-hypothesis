module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGermFunctionFieldIsFractionRingAffineChar
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFracChart

theorem isFractionRing_and_const (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens)
    (hUV : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (hρ : spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι) :
    (letI := ρ.toAlgebra; IsFractionRing Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField) ∧
      ∀ a : c.F, ρ (constFn TF.Y.s U.1 a) = GlobalTheory.Cartier.constFn (s₀ TF.Y Z) a := by
  set V := barComp TF.Y Z
  set W : (X₀ TF.Y Z).Opens := V.ι ⁻¹ᵁ U.1 with hWdef
  have hU : IsAffineOpen U.1 := U.2
  have hWU : V.ι ''ᵁ W = U.1 := by
    rw [hWdef, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUV
  have hW : IsAffineOpen W := by
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, hWU]; exact hU
  have hch : LogKS.chart U = hU.fromSpec := rfl
  have hcomp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g) x = g (f x) := fun _ _ _ => rfl
  have hη : genericPoint (X₀ TF.Y Z) ∈ W := by
    obtain ⟨p⟩ : Nonempty (Sp (X₀ TF.Y Z).functionField) := inferInstance
    have h1 : (spMap ρ ≫ LogKS.chart U) p ∈ U.1 := by
      rw [hcomp, hch]; show _ ∈ (U.1 : Set TF.Y.X); rw [← hU.range_fromSpec]; exact Set.mem_range_self _
    rw [hρ, hcomp] at h1
    exact GlobalTheory.Cartier.gen_mem (x := GlobalTheory.LogKSDiv.genPt TF Z p) h1
  set σ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField :=
    ((X₀ TF.Y Z).presheaf.germ W _ hη).hom.comp (V.ι.appLE U.1 W le_rfl).hom with hσ
  have key : spMap ρ ≫ hU.fromSpec = spMap σ ≫ hU.fromSpec := by
    rw [← hch, hρ, GlobalTheory.LogKSDiv.genPt, ← hW.fromSpecStalk_eq_fromSpecStalk hη, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec V.ι hU hW le_rfl, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hρe : ρ = σ := by
    have := Spec.map_injective ((cancel_mono hU.fromSpec).1 key)
    exact congrArg CommRingCat.Hom.hom this
  subst hρe
  haveI : Nonempty W := ⟨⟨_, hη⟩⟩
  have hle : U.1 ≤ V.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hUV
  haveI : IsIso (V.ι.app U.1) := Scheme.Hom.isIso_app V.ι U.1 hle
  have hFr : IsFractionRing Γ(X₀ TF.Y Z, W) (X₀ TF.Y Z).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ W hW
  refine ⟨?_, ?_⟩
  · letI := σ.toAlgebra
    exact IsFractionRing.of_ringEquiv_left (asIso (V.ι.app U.1)).commRingCatIsoToRingEquiv (fun x => by
      show σ x = _
      simp only [σ, RingHom.comp_apply, Scheme.Hom.app_eq_appLE]
      rfl)
  · intro a
    rw [← GlobalTheory.Cartier.fnOf_comp_algX (s₀ TF.Y Z) W hη]
    simp only [σ, RingHom.comp_apply]
    congr 1
    show ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ TF.Y.s.appLE ⊤ U.1 (fun _ _ => trivial) ≫
      V.ι.appLE U.1 W le_rfl).hom a = _
    have e := Scheme.Hom.appLE_comp_appLE V.ι TF.Y.s ⊤ U.1 W (fun _ _ => trivial) le_rfl
    erw [e]
    rfl

end GlobalTheory.GenFracChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffO
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS

set_option autoImplicit false

namespace GlobalTheory.ModifGeomConn

theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{0}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  infer_instance

theorem geometricallyConnected_modif : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  intro F _ X _ sX n _ U M _ _ hU
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have : GeometricallyIntegral sX := GlobalTheory.geometricallyIntegral_of_smooth sX
  obtain ⟨x, hx⟩ := hU
  have : Surjective (U.ι ≫ sX) := ⟨fun s => ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩⟩
  have h2 : GeometricallyConnected (U.ι ≫ sX) := geometricallyConnected_of_geometricallyIrreducible _
  have := M.iso
  have h3 : GeometricallyConnected (M.opn.ι ≫ M.str) := by
    have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ sX) := by
      rw [Modif.str, ← Category.assoc, ← Category.assoc, morphismRestrict_ι]
    rw [e]
    rw [GeometricallyConnected.eq_geometrically] at h2 ⊢
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 h2
  exact GlobalTheory.CompactVar.geometricallyConnected_of_denseRange M.opn.ι M.str
    (by rw [Scheme.Opens.range_ι]; exact M.dense)

end GlobalTheory.ModifGeomConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDualNumberCoordsOfAdicSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AdicDual

theorem hasSum_of_sumI {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} {C : Type} [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (h1 : ∀ a, ‖φ a‖ ≤ 1) (h2 : ∀ a ∈ I, ‖φ a‖ < 1)
    {M : Type} [AddCommGroup M] [Module R M] (g : M →+ C) (hg : ∀ (a : R) y, g (a • y) = φ a * g y)
    {Ix : Type} {x : Ix → M} {s : M} (h : GlobalTheory.UT.SumI I x s) : HasSum (fun i => g (x i)) (g s) := by
  have bd : ∀ {E : Type} [AddCommGroup E] [Module R E] (f : E →+ C), (∀ (a : R) y, f (a • y) = φ a * f y) →
      ∀ (t : Set E) (c : ℝ), 0 ≤ c → (∀ y ∈ t, ‖f y‖ ≤ c) → ∀ y ∈ Submodule.span R t, ‖f y‖ ≤ c := by
    intro E _ _ f hf t c h0 hc y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simpa using h0
    | add y z _ _ k1 k2 => rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2)
    | smul a y _ k1 => rw [hf, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (h1 a)).trans k1
  obtain ⟨N, ⟨t, rfl⟩, -, -, h⟩ := h
  obtain ⟨u, rfl⟩ := IsNoetherian.noetherian I
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ t, ‖g y‖ ≤ c :=
    ⟨∑ y ∈ t, ‖g y‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
      fun y hy => Finset.single_le_sum (f := fun y : M => ‖g y‖) (fun _ _ => norm_nonneg _) hy⟩
  obtain ⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ a ∈ u, ‖φ a‖ ≤ r :=
    ⟨(u.sup fun a => ‖φ a‖₊ : NNReal), NNReal.coe_nonneg _,
      by exact_mod_cast (Finset.sup_lt_iff (f := fun a => ‖φ a‖₊) (zero_lt_one' NNReal)).2 fun a ha =>
        show ‖φ a‖₊ < 1 from h2 a (Submodule.subset_span ha),
      fun a ha => by exact_mod_cast Finset.le_sup (f := fun a => ‖φ a‖₊) ha⟩
  have hI := bd φ.toAddMonoidHom (fun a y => map_mul φ a y) u r hr0 hr
  have hP : ∀ n : ℕ, ∀ y ∈ (Submodule.span R (u : Set R)) ^ n • Submodule.span R (t : Set M), ‖g y‖ ≤ r ^ n * c := by
    intro n
    induction n with
    | zero => simpa using bd g hg t c hc0 hc
    | succ n ih =>
      intro y hy
      rw [pow_succ', Submodule.mul_smul] at hy
      refine Submodule.smul_induction_on hy (fun a ha z hz => ?_)
        (fun y z k1 k2 => by rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2))
      rw [hg, norm_mul, pow_succ', _root_.mul_assoc]
      exact mul_le_mul (hI a ha) (ih z hz) (norm_nonneg _) hr0
  refine Metric.tendsto_nhds.2 fun e he => ?_
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const c
  rw [zero_mul] at lim
  obtain ⟨n, hn⟩ := (lim.eventually (gt_mem_nhds he)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.mem_of_superset (Filter.mem_atTop S) fun T hT => ?_
  show dist _ _ < e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dist_comm, dist_eq_norm, ← map_sum, ← map_sub]
  exact (hP n _ (hS T hT)).trans_lt hn

theorem hasSum_fst_snd : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (I : Ideal V) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V I C → ∀ {Ix : Type} (x : Ix → DualNumber V) (s : DualNumber V), GlobalTheory.UT.SumI I x s → HasSum (fun i => toF V C (x i).fst) (toF V C s.fst) ∧ HasSum (fun i => toF V C (x i).snd) (toF V C s.snd) := by
  intro V _ _ _ I C _ _ _ hC Ix x s h
  let φ : V →+* C := (algebraMap (FractionRing V) C).comp (algebraMap V _)
  constructor
  · exact hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.fstHom V V V).toLinearMap.toAddMonoidHom)
      (fun a y => by simp) h
  · exact hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.sndHom V V).toAddMonoidHom)
      (fun a y => by simp) h

end GlobalTheory.AdicDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT pbT)
open GlobalTheory.LogKS (IsField)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m : G.left ⟶ X) {m₁ : G.left ⟶ X} {L : LB X} {dd : Fin n → Fld G.left} {D : R → R} (h₁ : Heat G m₁ L dd D)

def W (p : h₁.J × (Fin 2 → L.ι)) : G.left.Opens := h₁.W p.1 ⊓ LB.wchart L ![m, m₁] p.2

theorem heatGaugeCoverOpen_le_heatOperatorOpen (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ h₁.W p.1 := inf_le_left

theorem W_le_wchart (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ LB.wchart L ![m, m₁] p.2 := inf_le_right

theorem W_le_m (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m ⁻¹ᵁ L.U (p.2 0) :=
  (W_le_wchart m h₁ p).trans (LB.wchart_le L ![m, m₁] p.2 0)

theorem W_le_m₁ (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m₁ ⁻¹ᵁ (L.U (p.2 1) ⊓ L.U (h₁.j p.1)) :=
  fun _ hy => ⟨LB.wchart_le L ![m, m₁] p.2 1 hy.2, h₁.le p.1 hy.1⟩

variable (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

def gU (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p)ˣ :=
  res (W_le_wchart m h₁ p) (e.s p.2) * res (W_le_m₁ m h₁ p) (pullU m₁ _ (L.g (p.2 1) (h₁.j p.1)))

def gL (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  dd a (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gE (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  h₁.d p.1 (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gY (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e b p

def gD (p : h₁.J × (Fin 2 → L.ι)) : Fld G.left :=
  fun O f => h₁.d p.1 O f + ∑ a, rsT (gY m h₁ e a p) O * dd a O f

def gP (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p p.1) (W m h₁ p) - gE m h₁ e p -
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e a p * gL m h₁ e b p

def gP' (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p' p.1) (W m h₁ p) +
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * dd a (W m h₁ p) (gL m h₁ e b p) -
    ∑ a, constFn G.hom (W m h₁ p) (h₁.u a) * gL m h₁ e a p

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : Fld Z} (h : IsField W₀ d) (hle : W₁ ≤ W₀) :
    IsField W₁ d :=
  ⟨fun W hW => h.1 W (hW.trans hle), fun W hW => h.2.1 W (hW.trans hle),
    fun W W' hWW' hW => h.2.2 W W' hWW' (hW.trans hle)⟩


open GlobalTheory.KS in
theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (dd : Fin n → Fld G.left) (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R)
    (d : Fld G.left) {W₀ : G.left.Opens} (p p' : Γ(G.left, W₀)) (k : ℕ) {O O' : G.left.Opens}
    (hd : IsField O d) (hO : O ≤ W₀) (h : O' ≤ O) (f : Γ(G.left, O)) :
    rsT (op G dd Θ u d p p' k O f) O' = op G dd Θ u d p p' k O' (rsT f O') := by
  have hd' : ∀ g, resG G.left h (d O g) = d O' (resG G.left h g) :=
    fun g => (hd.2.2 O O' h le_rfl g).symm
  have hdd' : ∀ a g, resG G.left h (dd a O g) = dd a O' (resG G.left h g) :=
    fun a g => ((hdd a).2.2 O O' h le_top g).symm
  have hc : ∀ r, resG G.left h (constFn G.hom O r) = constFn G.hom O' r :=
    fun r => (rsT_of_le h _).symm.trans (rsT_constFn G.hom h r)
  have hp : ∀ q : Γ(G.left, W₀), resG G.left h (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h, rsT_rsT hO h]
  rw [rsT_of_le h, rsT_of_le h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem trans_factor {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : GlobalTheory.RayEv.Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) :
    ∃ τ : Q.P.A.left ⟶ Q.P.A.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left = Y.q.left ≫ τ := by
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  refine ⟨(𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)).left, ?_⟩
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc Y.q (toUnit _),
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg (fun f => f.left) e

end GlobalTheory.Heat.Gauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeOneOfGoingDownZariski
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.ZariskiDescent

theorem dvr_dvd_pow_of_mem_maximalIdeal {L : Type} [Field L] (V : ValuationSubring L)
    [IsDiscreteValuationRing V] (x y : V) (hx : x ∈ IsLocalRing.maximalIdeal V) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ x ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton'] at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨n, ⟨z ^ n * ↑u⁻¹, ?_⟩⟩
  rw [hu, mul_pow]
  have : (↑u * ↑u⁻¹ : V) = 1 := Units.mul_inv u
  linear_combination (-(z ^ n * ϖ ^ n)) * this

theorem mem_of_nonunits_of_localization {L : Type} [Field L] (V : ValuationSubring L)
    [IsDiscreteValuationRing V] {A : Type} [CommRing A] (ι : A →+* L) (hι : Function.Injective ι)
    (hV : ∀ a, ι a ∈ V)
    (hloc : ∀ s ∈ V, ∃ b d : A, ι d ≠ 0 ∧ (ι d)⁻¹ ∈ V ∧ s = ι b / ι d)
    (P₁ : Ideal A) [P₁.IsPrime] (hne : P₁ ≠ ⊥) (hP₁ : ∀ z ∈ P₁, ι z ∈ V.nonunits) :
    ∀ x, ι x ∈ V.nonunits → x ∈ P₁ := by
  intro x hx
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hyV : (⟨ι y, hV y⟩ : V) ≠ 0 := by
    intro h
    apply hy0
    apply hι
    simpa using congrArg Subtype.val h
  have hxV : (⟨ι x, hV x⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
    ValuationSubring.coe_mem_nonunits_iff.mp hx
  obtain ⟨n, w, hw⟩ := dvr_dvd_pow_of_mem_maximalIdeal V _ _ hxV hyV
  obtain ⟨b, d, hd0, hdinv, hwbd⟩ := hloc (w : L) w.2
  have hL : ι x ^ n = ι y * (ι b / ι d) := by
    have := congrArg Subtype.val hw
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul] at this
    rw [this, ← hwbd]
    rfl
  have hA : x ^ n * d = y * b := by
    apply hι
    rw [map_mul, map_mul, map_pow, hL]
    field_simp
  have hmem : x ^ n * d ∈ P₁ := by
    rw [hA]; exact P₁.mul_mem_right b hyP
  rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
  · exact Ideal.IsPrime.mem_of_pow_mem ‹_› n h
  · exfalso
    have := (ValuationSubring.mem_nonunits_iff_or (A := V)).mp (hP₁ d h)
    rcases this with h1 | h1
    · exact hd0 h1
    · exact h1 hdinv

end GlobalTheory.ZariskiDescent

namespace GlobalTheory.ZariskiDescent

theorem comap_nonunits_iff {K L : Type} [Field K] [Field L] (φ : K →+* L) (V : ValuationSubring L)
    (x : K) : x ∈ (V.comap φ).nonunits ↔ φ x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem height_le_one_of_going_down :
    ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L)
      [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) →
      R ≤ (V.comap φ).toSubring → ∀ t : Finset L,
      (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) →
      (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t),
        ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) →
      ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) →
      ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := by
  intro K L _ _ φ c V _ R _ hc hRV t ht hloc p hp hp0 hpq
  letI : Algebra R L := (φ.comp R.subtype).toAlgebra
  have halg : ∀ r : R, algebraMap R L r = φ r := fun r => rfl
  set S : Subalgebra R L := Algebra.adjoin R (t : Set L) with hSdef
  have hinjRL : Function.Injective (algebraMap R L) := by
    intro a b h
    rw [halg, halg] at h
    exact Subtype.ext (φ.injective h)
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjRL
    have := congrArg Subtype.val h
    simpa using this
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.adjoin (fun x hx => by
    obtain ⟨-, q, hq, hqx⟩ := ht x hx
    exact ⟨q, hq, hqx⟩)
  haveI : Algebra.HasGoingDown R S := inferInstance

  have hSV : ∀ z ∈ S, z ∈ V := by
    intro z hz
    have hz' : z ∈ S.toSubring := hz
    rw [hSdef, Algebra.adjoin_eq_ring_closure] at hz'
    refine (Subring.closure_le (t := V.toSubring)).mpr ?_ hz'
    rintro w (⟨r, rfl⟩ | hw)
    · exact (ValuationSubring.mem_comap).mp (hRV r.2)
    · exact (ht w hw).1

  have hclS : Subring.closure (Set.range (φ.comp c) ∪ ↑t) ≤ S.toSubring := by
    rw [Subring.closure_le]
    rintro w (⟨a, rfl⟩ | hw)
    · have : (φ.comp c) a = algebraMap R L ⟨c a, hc a⟩ := rfl
      rw [this]
      exact S.algebraMap_mem _
    · exact Algebra.subset_adjoin hw
  let ι : S →+* L := algebraMap S L
  have hι : Function.Injective ι := Subtype.val_injective
  let f : S →+* V := ι.codRestrict V (fun z => hSV z.1 z.2)
  let P : Ideal S := Ideal.comap f (IsLocalRing.maximalIdeal V)
  haveI : P.IsPrime := Ideal.comap_isPrime f _
  have hPmem : ∀ z : S, z ∈ P ↔ (z : L) ∈ V.nonunits := by
    intro z
    show f z ∈ IsLocalRing.maximalIdeal V ↔ _
    exact ValuationSubring.coe_mem_nonunits_iff.symm
  let q : Ideal R := P.comap (algebraMap R S)
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver q := ⟨rfl⟩
  have hqmem : ∀ r : R, r ∈ q ↔ (r : K) ∈ (V.comap φ).nonunits := by
    intro r
    show algebraMap R S r ∈ P ↔ _
    rw [hPmem, comap_nonunits_iff]
    rfl
  have hpq' : p ≤ q := fun r hr => (hqmem r).mpr (hpq r hr)
  obtain ⟨P₁, hP₁P, hP₁, hP₁o⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q) P hpq'
  have hpover : p = P₁.comap (algebraMap R S) := hP₁o.over
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    apply hp0
    rw [hpover, h, eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    apply hinjRL
    have := congrArg Subtype.val hr
    simpa using this
  have key := mem_of_nonunits_of_localization V ι hι (fun a => hSV a.1 a.2)
    (by
      intro s hs
      obtain ⟨b, hb, d, hd, hd0, hdinv, rfl⟩ := hloc s hs
      exact ⟨⟨b, hclS hb⟩, ⟨d, hclS hd⟩, hd0, hdinv, rfl⟩)
    P₁ hP₁ne (fun z hz => (hPmem z).mp (hP₁P hz))
  intro r hr
  rw [hpover, Ideal.mem_comap]
  apply key
  exact (hPmem _).mp ((hqmem r).mpr hr)

end GlobalTheory.ZariskiDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestMore
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.GenInterior

theorem exists_j₀_eq_genericPoint (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] :
    ∃ v : V₀ TF.Y Z, j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  obtain ⟨x, hx⟩ := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  have hxm : TF.Y.j x ∈ barComp TF.Y Z := (j_mem_barComp Z x).2 hx
  let v : V₀ TF.Y Z := ⟨x, hxm⟩
  have hU : IsOpen (Set.range (j₀ TF.Y Z)) := (j₀ TF.Y Z).isOpenEmbedding.isOpen_range
  exact ((genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff hU).2 ⟨j₀ TF.Y Z v, trivial, v, rfl⟩

end GlobalTheory.GenInterior
end

