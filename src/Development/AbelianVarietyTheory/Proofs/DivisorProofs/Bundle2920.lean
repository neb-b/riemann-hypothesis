module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AutomorphicArithmetic.LocalEmbeddings.ArchFlip
public import Development.AutomorphicArithmetic.DivisorFrames.ConjSizeHeckeCharLocalOfMemRangeEmbedding
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataBoundOfHalfFlip
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedHeatOperatorsPreserveSectionsUpToConstant
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatVExt
open GlobalTheory.KS

theorem cst_resV {Y : Scheme.{0}} {R : Type} [CommRing R] (π : Y ⟶ Sp R) (c : R) {O : Y.Opens}
    (h : O ≤ π ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1) (r : R) :
    GlobalTheory.HeatV.cst π _ h (GlobalTheory.HeatV.resV R c r) = rsT (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) O := by
  rw [rsT_of_le le_top]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.map_appLE π (U := (GlobalTheory.HeatV.bo R c).1) (U' := ⊤) (V := O) h (homOfLE le_top).op)

theorem rsT_cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O O' : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O)
    (a : Γ(X, V)) : rsT (GlobalTheory.HeatV.cst π V h a) O' = GlobalTheory.HeatV.cst π V (h'.trans h) a := by
  rw [rsT_of_le h']
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_map π h (homOfLE h').op)

theorem rsT_natCast {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (m : ℕ) : rsT (m : Γ(Y, O₀)) O = m := by
  rw [rsT_of_le h, map_natCast]

theorem rsT_two {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) : rsT (2 : Γ(Y, O₀)) O = 2 := by
  rw [rsT_of_le h, map_ofNat]

theorem opV_rsT : ∀ {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → GlobalTheory.Heat.Fld Y), (∀ a, IsField ⊤ (dd a)) → ∀ (Θ : Matrix (Fin n) (Fin n) Γ(X, V)) (u : Fin n → Γ(X, V)) (d : GlobalTheory.Heat.Fld Y) {W : Y.Opens}, IsField W d → ∀ (p p' : Γ(Y, W)) (k : ℕ) {O O' : Y.Opens} (hOW : O ≤ W) (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O) (f : Γ(Y, O)), rsT (GlobalTheory.HeatV.opV π V dd Θ u d p p' k O h f) O' = GlobalTheory.HeatV.opV π V dd Θ u d p p' k O' (h'.trans h) (rsT f O') := by
  intro Y X π V n dd hdd Θ u d W hd p p' k O O' hOW h h' f
  have hd' : ∀ g, resG Y h' (d O g) = d O' (resG Y h' g) :=
    fun g => ((hd.2.2 O O' h' hOW g)).symm
  have hdd' : ∀ a g, resG Y h' (dd a O g) = dd a O' (resG Y h' g) :=
    fun a g => ((hdd a).2.2 O O' h' le_top g).symm
  have hc : ∀ r, resG Y h' (GlobalTheory.HeatV.cst π V h r) = GlobalTheory.HeatV.cst π V (h'.trans h) r :=
    fun r => (rsT_of_le h' _).symm.trans (rsT_cst π V h h' r)
  have hp : ∀ q : Γ(Y, W), resG Y h' (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h', rsT_rsT hOW h']
  rw [rsT_of_le h', rsT_of_le h']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.HeatV.opV, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem heat_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (dd' : Fin n → Fld t.G.left), (∀ a, IsField ⊤ (dd' a)) → ∀ (D : Derivation ℤ R R) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∀ (k : ℕ) (σ : SecM (𝟙 t.G.left) t.PP.L k) (a : R), ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k), r ≠ 0 ∧ ∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t c hc n dd' hdd' D Θ₁ DV hDV J W j d u pf pf' hW hcov hWL hd hdc hglue k σ a
  set π := t.G.hom
  set M := LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)) with hMdef
  have hM : M.IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  set f : Γ(t.G.left, ⊤) := π.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) with hfdef
  have hb : π ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 = t.G.left.basicOpen f := Scheme.preimage_basicOpen_top π _
  have hWc : ∀ i, W i ≤ M.U (fun _ => j i) := fun i => GlobalTheory.Heat.Glue.le_wchart _ (hWL i)
  let F : ∀ i, Γ(t.G.left, W i) := fun i =>
    GlobalTheory.HeatV.cst π _ (hW i) (GlobalTheory.HeatV.resV R c a) *
                 GlobalTheory.HeatV.opV π _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) -
      2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst π _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) *
        rsT (σ.f fun _ => j i) (W i)
  have hF : ∀ i i', rsT (F i) (W i ⊓ W i') =
      rsT (M.g (fun _ => j i) (fun _ => j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i') := by
    intro i i'
    have hII : W i ⊓ W i' ≤ M.U (fun _ => j i) ⊓ M.U (fun _ => j i') := inf_le_inf (hWc i) (hWc i')
    have hs := GlobalTheory.Heat.Glue.sec_rel (𝟙 t.G.left) k σ (fun _ => j i) (fun _ => j i') hII
    have hgl := hglue k i i' (W i ⊓ W i') le_rfl (rsT (σ.f fun _ => j i') (W i ⊓ W i'))
    rw [GlobalTheory.Heat.Glue.linComb_g (𝟙 t.G.left) k _ _ hII]
    simp only [F, rsT_sub, rsT_mul, rsT_cst _ _ _ inf_le_left, rsT_cst _ _ _ inf_le_right,
      rsT_natCast inf_le_left, rsT_natCast inf_le_right, rsT_two inf_le_left, rsT_two inf_le_right]
    rw [opV_rsT π _ dd' hdd' Θ₁ u (d i) (hd i) (pf i) (pf' i) k le_rfl (hW i) inf_le_left,
      opV_rsT π _ dd' hdd' Θ₁ u (d i') (hd i') (pf i') (pf' i') k le_rfl (hW i') inf_le_right,
      rsT_rsT (hWc i) inf_le_left, rsT_rsT (hWc i') inf_le_right, hs, hgl]
    ring
  haveI := t.semi.quasiCompact
  haveI := t.semi.separated
  haveI : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  haveI : QuasiSeparatedSpace t.G.left := quasiSeparatedSpace_of_quasiSeparated t.G.hom
  obtain ⟨tt, htt, htF⟩ := _root_.GlobalTheory.GlueOver.exists_glue M hM (t.G.left.basicOpen f) W (fun i _ => j i) F (by rw [hcov, hb]) hWc hF
  obtain ⟨N, s, hs⟩ := _root_.GlobalTheory.SecAff.sec_extend_basicOpen t.G.left M hM f tt htt
  refine ⟨c ^ N, s, pow_ne_zero N hc, fun i => ?_⟩
  have hWi : W i ≤ M.U (fun _ => j i) ⊓ t.G.left.basicOpen f := le_inf (hWc i) (hb ▸ hW i)
  refine (rsT_rsT inf_le_left hWi _).symm.trans ?_
  refine (congrArg (fun x => rsT x (W i)) (hs (fun _ => j i))).trans ?_
  rw [rsT_mul, GlobalTheory.Heat.Glue.rsT_pow' hWi, rsT_rsT le_top hWi,
    htF i, map_pow, map_pow, cst_resV]

end GlobalTheory.HeatVExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermValuesEqOfLocalIdentity
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem sval_eq_of_localIdentity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → ∀ c : ℕ → Q.X → R, (∀ (i : h.J) (i' : h'.J) (k : ℕ) (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ (c k α) * f)) → ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (c k α)) * sval σ x.left z J := by
  intro R _ _ Q O _ _ _ oa Y n v dd hv D h h' hb hb' c hc k α σ σ' σ'' ⟨τ₁, τ₁', t1, t1', a1⟩ ⟨τ₂, τ₂'', t2, t2'', a2⟩ T x z J hJ
  refine _root_.GlobalTheory.FourierDescent.values_identity R Q O oa Y k α σ σ' σ'' (c k α) ?_ T x z J hJ
  intro y J' hJ'
  have e : ∀ (s : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α s τ →
      sval τ (𝟙 Y.H.left) y J' = sval s Y.q.left y J' * (val ((Y.Φ Y.H (𝟙 _)).s α) (𝟙 _) y J').val := by
    intro s τ hτ
    have := hτ Y.H (𝟙 _) y J' hJ'
    simpa only [Over.id_left, Category.id_comp] using this
  have key := _root_.GlobalTheory.HeatUniq.FourierChart.images_eq R Q O oa Y n dd D (fun a => (hv a).1) h h' hb hb' k α (c k α) (fun i i' => hc i i' k α) τ₁ τ₁' τ₂ τ₂''
    (fun y J hJ => by
      have a := t1 Y.H (𝟙 _) y J hJ
      have b := t2 Y.H (𝟙 _) y J hJ
      simp only [Over.id_left, Category.id_comp] at a b
      rw [a, b])
    (_root_.GlobalTheory.Heat.isWt_rsT_of_isTerm R Q O oa Y k α σ τ₂ t2) a1 a2 y J' hJ'
  rw [e σ' τ₁' t1', e σ'' τ₂'' t2'', e σ τ₂ t2] at key
  set u := val ((Y.Φ Y.H (𝟙 _)).s α) (𝟙 _) y J'
  have : (sval σ' Y.q.left y J' - (sval σ'' Y.q.left y J' + gs (𝟙 _) y ⊤ (scal Y.H.hom (c k α)) * sval σ Y.q.left y J')) * u.val = 0 := by
    rw [sub_mul, key]; ring
  have h0 := congrArg (· * (u⁻¹ : (Y.H.left.presheaf.stalk y)ˣ).val) this
  simp only [Units.mul_inv_cancel_right, zero_mul] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.Heat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatLoc

variable {F : Type} [Field F]

theorem der_bracket (d : Derivation ℤ F F) (x y β : F) (M : ℕ) :
    x * β ^ M * d (y * β ^ M) - y * β ^ M * d (x * β ^ M) = β ^ (2 * M) * (x * d y - y * d x) := by
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

theorem der_mul_pow (d : Derivation ℤ F F) (x β : F) (hβ : β ≠ 0) (m : ℕ) :
    d (x * β ^ (m + 1)) = β ^ (m + 1) * (d x + ((m + 1 : ℕ) : F) * x * (d β / β)) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  field_simp
  ring

theorem symb_eq {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (hβ : β ≠ 0) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * (x * β ^ (m + 1)) * (x * β ^ (m + 1) * δ₀ (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ₀ (x * β ^ (m + 1))) -
      ∑ a, ∑ e, Λ a e * δ a (x * β ^ (m + 1)) *
        (x * β ^ (m + 1) * δ e (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ e (x * β ^ (m + 1))) =
    β ^ (3 * (m + 1)) * (((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x)) := by
  rw [mul_sub (β ^ (3 * (m + 1))), Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · rw [der_bracket]; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [der_bracket, der_mul_pow _ _ _ hβ]; ring

theorem symb_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * 1 * (1 * δ₀ y - y * δ₀ 1) -
      ∑ a, ∑ e, Λ a e * (δ a 1 + ((m + 1 : ℕ) : F) * 1 * (δ a β / β)) * (1 * δ e y - y * δ e 1) =
    ((m + 1 : ℕ) : F) * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) := by
  simp only [Derivation.map_one_eq_zero, mul_zero, sub_zero, zero_add, one_mul, mul_one]
  rw [mul_sub, Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · push_cast; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring

def derivationBracketSum {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) : F :=
  ∑ a, ∑ e, Λ a e * δ a x * (x * δ e y - y * δ e x)

theorem symb_two {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
    ((m + 1 : ℕ) : F) * x * (x * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) -
      y * ((k : F) * δ₀ x - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x)) - derivationBracketSum δ Λ x y := by
  have hs : ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
      derivationBracketSum δ Λ x y + ((m + 1 : ℕ) : F) * x * (x * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y -
        y * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x) := by
    unfold derivationBracketSum
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs]; push_cast; ring

theorem tsum_add_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) :
    derivationBracketSum δ Λ (x + 1) y - derivationBracketSum δ Λ x y = ∑ a, ∑ e, Λ a e * δ a x * δ e y := by
  unfold derivationBracketSum
  simp only [map_add (f := _), Derivation.map_one_eq_zero, add_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  ring

end GlobalTheory.HeatLoc

namespace GlobalTheory.HeatLoc

theorem valR_ne_zero_sec {X : Scheme.{0}} (L : LB X) {F : Type} [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι)
    (h : ⊤ ≤ ξ ⁻¹ᵁ L.U j₀) (k : ℕ) (s : SecM (𝟙 X) L k) (hs : ⊤ ≤ ξ ⁻¹ᵁ nonzeroLocus s) :
    valR ξ _ (s.f fun _ => j₀) ≠ 0 := by
  have hk : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) fun _ => (k : ℤ)).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => h hp
  have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff ξ (IsLocalRing.closedPoint F) _ (hk trivial) _).1
    ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs s ξ _ (hk trivial)).1 (hs trivial))
  exact ((GlobalTheory.Points.le_preimage_basicOpen_iff ξ hk _).1
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of F) ξ h₁).ge).ne_zero

theorem symb_regular : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → ∀ (k : ℕ), 1 ≤ k → ∀ s : SecM (𝟙 P₀.A.left) P₀.L k, ⊤ ≤ ξ ⁻¹ᵁ (Out.nonzeroLocus s) → (∀ f f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ h : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) ∧ (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a (valR ξ _ (s.f fun _ => j₀)) / valR ξ _ (s.f fun _ => j₀)) * δ e (valR ξ _ f)) := by
  intro K _ _ P₀ n v dd hdd F _ ψ ξ hξ hinj δ hδ j₀ hj₀ δ₀ Λ hyp k hk s hs
  haveI := P₀.isAb.proper
  haveI : CompactSpace P₀.A.left := QuasiCompact.compactSpace_of_compactSpace P₀.A.hom
  haveI : QuasiSeparatedSpace P₀.A.left := quasiSeparatedSpace_of_quasiSeparated P₀.A.hom
  obtain ⟨G₁, G₂⟩ := _root_.GlobalTheory.SecQuot.valR_secM_eq_mul_pow P₀.A.left P₀.L P₀.isLB F ξ j₀ hj₀ k s hs
  have hβ := valR_ne_zero_sec P₀.L ξ j₀ hj₀ k s hs
  set β := valR ξ _ (s.f fun _ => j₀) with hβdef
  have v1 : valR ξ (nonzeroLocus s) 1 = 1 := by rw [WtAlg.valR_eq' ξ _ hs, map_one, map_one]
  have hM : ∀ m : ℕ, ((m + 1 : ℕ) : F) ≠ 0 := fun m h => by
    have : ψ ((m + 1 : ℕ) : K) = 0 := by rw [map_natCast]; exact h
    exact (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)) ((map_eq_zero ψ).1 this)

  have partD : ∀ f : Γ(P₀.A.left, nonzeroLocus s), ∃ f' : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f) := by
    intro f
    obtain ⟨m₁, h₁⟩ := G₁ 1
    obtain ⟨m₂, h₂⟩ := G₁ f
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, v1, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_one] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * ((k : F) * δ₀ (valR ξ _ f) -
        ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f)) := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨constFn P₀.A.hom _ (((m + 1 : ℕ) : K)⁻¹) * g, ?_⟩
    rw [WtAlg.valR_mul'' ξ _ hs, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ hs hξ, e', map_inv₀, map_natCast,
      ← _root_.mul_assoc, inv_mul_cancel₀ (hM m), _root_.one_mul]

  have partT : ∀ f f' : Γ(P₀.A.left, nonzeroLocus s), ∃ h : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ h = derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
    intro f f'
    obtain ⟨m₁, h₁⟩ := G₁ f
    obtain ⟨m₂, h₂⟩ := G₁ f'
    obtain ⟨d, hd⟩ := partD f
    obtain ⟨d', hd'⟩ := partD f'
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_two, ← hd, ← hd'] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * valR ξ _ f * (valR ξ _ f * valR ξ _ d' - valR ξ _ f' * valR ξ _ d) -
        derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨((m + 1 : ℕ) : Γ(P₀.A.left, nonzeroLocus s)) * f * (f * d' - f' * d) - g, ?_⟩
    rw [WtAlg.valR_sub' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_sub' ξ _ hs,
      WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_natCast' ξ _ hs, e']
    ring
  refine ⟨fun f f' => ?_, partD⟩
  obtain ⟨h₁, e₁⟩ := partT (f + 1) f'
  obtain ⟨h₂, e₂⟩ := partT f f'
  refine ⟨h₁ - h₂, ?_⟩
  rw [WtAlg.valR_sub' ξ _ hs, e₁, e₂, WtAlg.valR_add' ξ _ hs, v1, tsum_add_one]

end GlobalTheory.HeatLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationsOrthogonalLineBundlePairingProdu
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.HodgeOrth

theorem fv_sum {R : Type} [CommRing R] {X : Over (Sp R)} {J : Type} (s : Finset J) (c : J → R)
    (α : J → Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (∑ i ∈ s, c i • α i) D D' φ x = ∑ i ∈ s, fv (α i) D D' φ x * algebraMap R D' (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i s hi ih =>
    obtain ⟨hadd, hsmul, _⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear R X
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, Fn1.add, hsmul, ih,
      mul_comm (algebraMap R D' (c i))]

theorem commAlgFunctorCocyclesTwo_finsetSum_apply {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {J : Type}
    (s : Finset J) (w : J → Z2 F) (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (∑ i ∈ s, w i).1 T T' T'' φ ψ = ∑ i ∈ s, (w i).1 T T' T'' φ ψ := by
  simp only [Submodule.coe_sum, Finset.sum_apply]

theorem sum_cup_eq_mk {R : Type} [CommRing R] {A B : Over (Sp R)} {N : ℕ}
    (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Fin N → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ (α k)))
      (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ (β k)))) =
      CatCoh.H2.mk _ (∑ k, cupZ _ (m₁.coef.pullbackOneCocycle (α k)) (m₂.coef.pullbackOneCocycle (β k))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← cup_mk]
  rfl

theorem exists_isCupCob {R : Type} [CommRing R] {A B : Over (Sp R)} {N : ℕ} (P : LB (A ⊗ B).left)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Fin N → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (hc : IsChern (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P
      (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ (α k)))
        (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ (β k))))) :
    ∃ n, IsCupCob P.U (fun i ↦ fv (α i)) (fun i ↦ fv (β i)) n := by
  have m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  rw [sum_cup_eq_mk m₁ m₂] at hc
  obtain ⟨n, hn⟩ := GlobalTheory.PtExt.exists_pointwiseCochain_coboundary_eq_chernCocycle R (A ⊗ B) P _ hc
  refine ⟨n, ?_⟩
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  rw [hn E E' E'' φ ψ z hz, commAlgFunctorCocyclesTwo_finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ _root_.GlobalTheory.PtExt.cupZ_pull_apply_fv R A B m₁ m₂ _ _ E E' E'' φ ψ z

theorem sum_mem_F1prim {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {N : ℕ} (a : Fin N → primDR A)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (hα : ∀ i, CatCoh.H1.mk _ (α i) = (a i).1) (c : Fin N → R)
    (k : Fn0 A)
    (hk : IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, fv (α i) D D' φ x * algebraMap R D' (c i)) k) :
    ∑ i, c i • a i ∈ PrimitiveSubmodule A := by
  have hF : CatCoh.H1.mk _ (∑ i, c i • α i) ∈ F1 (A.hom ≫ 𝟙 _) := by
    have hfv : fv (∑ i, c i • α i) =
        ((fun D _ _ D' _ _ φ x ↦ ∑ i, fv (α i) D D' φ x * algebraMap R D' (c i)) : Fn1 A) := by
      funext D _ _ D' _ _ φ x
      exact fv_sum Finset.univ c α D D' φ x
    apply (mem_hodgeFiltration_iff_pointwiseCoboundary R A _).2
    rw [hfv]
    exact ⟨k, hk⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hF
  simp only [map_smul, hα] at hF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PrimitiveSubmodule, Submodule.mem_comap, map_sum]
  exact hF

theorem fil_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro H R _ A B _ _ g _ hB _ gB P hP φ hP' x hx y hy
  obtain ⟨N, a, b, hc, hφ⟩ := hP'
  choose α hα using fun k ↦ CatCoh.H1.mk_surjective _ (a k).1
  choose β hβ using fun k ↦ CatCoh.H1.mk_surjective _ (b k).1
  obtain ⟨n, hcup⟩ := exists_isCupCob P α β (by simp only [hα, hβ]; exact hc)
  have hβ' : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B := fun i ↦ by rw [hβ]; exact (b i).2
  obtain ⟨k, hk⟩ := GlobalTheory.PtExt.OrthPt.exists_isCob_of_mem_fil H R A B g hB gB _ P.U hP.cover (Fin N) _ β hβ' n
    (fun i ↦ (fv_isCoc_and_ev_eq R A (α i)).1) hcup y hy
  have eb : ∀ i, (⟨_, hβ' i⟩ : primDR B) = b i := fun i ↦ Subtype.ext (hβ i)
  have h0 := (Submodule.mem_dualAnnihilator _).1 hx _ (sum_mem_F1prim a α hα _ k hk)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hφ, ← h0, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, mul_comm, eb]

end GlobalTheory.PtExt.HodgeOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTensorBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem infTensAt_of_places {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) {C : ℝ} (hC : 0 ≤ C)
    (hd : DatAt ch (C / 2)) (hc : CoefAt ch (C / 2)) : InfTensAt ch C := by
  intro σ Φ β hβ x y
  set K : ℝ := C / 2 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hK
  have h1 := absLe_prod (Finset.univ : Finset (locPl ch.G A.μ0)) (σ := σ)
    (fun v => ((ch.S.term A.μ0 Φ β v).coef : ℂ)) (fun v => K * placeSz ch.G v)
    (fun v _ => absLe_rat σ _ (by simpa [hK] using hc Φ β hβ v))
  have h2 := absLe_prod (Finset.univ : Finset (locPl ch.G A.μ0)) (σ := σ)
    (fun v => (ch.S.term A.μ0 Φ β v).datum (ch.S.colAt A.μ0 v x) (ch.S.rowAt A.μ0 v y)) (fun v => K * placeSz ch.G v)
    (fun v _ => by simpa [hK] using hd σ Φ β hβ v x y)
  refine absLe_mono (absLe_mul h1 h2) ?_
  rw [← Finset.mul_sum, ← two_mul, ← mul_assoc]
  have : 2 * K = C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 := by rw [hK]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (sum_placeSz_le ch.G A.μ0) (by positivity)

end GlobalTheory.ArchTens


end
end

