module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaugedTorusInvariantHeatOperator
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

open GlobalTheory.KS

theorem gauge_op {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hdd : ∀ a, IsField ⊤ (dd a)) (c : R) (hc : 2 * c = 1)
    (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens) (hO : O ≤ W m h₁ p) (f : Γ(G.left, O)) :
    op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k O (rsT (gU m h₁ e p).val O ^ k * f) =
      rsT (gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f :=
  _root_.GlobalTheory.Heat.Gauge.op_gauged _ G n X m m₁ L dd D h₁ e hdd c hc p k O hO f

theorem gauge_cocycle {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (p p' : h₁.J × (Fin 2 → L.ι))
    (O : G.left.Opens) (hO : O ≤ W m h₁ p ⊓ W m h₁ p') :
    pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (gU m h₁ e p').val O =
      rsT (gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O :=
  _root_.GlobalTheory.Heat.Gauge.gU_transition _ G n X m m₁ L dd D h₁ e hL he p p' O hO

theorem gauge_chart {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (k : ℕ) (σ : SecM m₁ L k)
    (ρ : SecM m L k)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val)
    (p : h₁.J × (Fin 2 → L.ι)) :
    rsT (ρ.f fun _ => p.2 0) (W m h₁ p) = (gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (W m h₁ p) :=
  _root_.GlobalTheory.Heat.Gauge.chart_fn_mul_gen_pow _ G n X m m₁ L dd D h₁ e hL he k σ ρ hρ p

theorem gauge_wt {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R)
    (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D)
    (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X)
    (hwe : ∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens),
      Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j →
        IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))
    (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens) (hV : Y.q.left ⁻¹ᵁ V ≤ W Y.q.left h₁ p) :
    IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) :=
  _root_.GlobalTheory.Heat.Gauge.gU_isWt _ Q O oa Y n dd D x h₁ e β hwe p V hV

section General

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
  (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

theorem gauge_cover (hL : L.IsLB) : ⨆ p, W m h₁ p = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  have hy : y ∈ ⨆ i, h₁.W i := by rw [h₁.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (m y)
  obtain ⟨b, hb⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (m₁ y)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, ![a, b]), hi, Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨ha, hb⟩)⟩

theorem gauge_lift (hF : ∀ a, IsField ⊤ (dd a)) (h0 : ∀ a O r, dd a O (constFn G.hom O r) = 0)
    (p : h₁.J × (Fin 2 → L.ι)) : IsLift G D (W m h₁ p) (gD m h₁ e p) := by
  have hd₁ := h₁.lift p.1
  refine ⟨GlobalTheory.Heat.Adjust.isField_add_comb (h₁.d p.1) dd (fun a => gY m h₁ e a p)
    (isField_mono hd₁.1 (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) hF, fun O' hO r => ?_⟩
  show h₁.d p.1 O' (constFn G.hom O' r) + ∑ a, rsT (gY m h₁ e a p) O' * dd a O' (constFn G.hom O' r) = _
  rw [hd₁.2 O' (hO.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) r]
  simp [h0]

theorem gauge_glue (hL : L.IsLB) (he : e.IsGen) (hF : ∀ a, IsField ⊤ (dd a)) (c : R) (hc : 2 * c = 1) (k : ℕ)
    (p p' : h₁.J × (Fin 2 → L.ι)) (O' : G.left.Opens) (hO : O' ≤ W m h₁ p ⊓ W m h₁ p') (f : Γ(G.left, O')) :
    op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k O' (pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f) =
      pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k *
        op G dd h₁.Θ h₁.u (gD m h₁ e p') (gP m h₁ e c p') (gP' m h₁ e c p') k O' f := by
  have hOp : O' ≤ W m h₁ p := hO.trans inf_le_left
  have hOp' : O' ≤ W m h₁ p' := hO.trans inf_le_right
  have hco := gauge_cocycle G m m₁ L dd D h₁ e hL he p p' O' hO
  have hA' : rsT (gU m h₁ e p').val O' * rsT (gU m h₁ e p')⁻¹.val O' = 1 := by
    rw [← GlobalTheory.KS.rsT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.KS.rsT_one hOp']
  have hk := congrArg (· ^ k) hco
  have hk' := congrArg (· ^ k) hA'
  simp only [one_pow, mul_pow] at hk hk'
  have e1 : pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f =
      rsT (gU m h₁ e p).val O' ^ k *
        (pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O' ^ k * (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f)) := by
    linear_combination (-(pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f)) * hk' +
      (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f) * hk
  have ef : f = rsT (gU m h₁ e p').val O' ^ k * (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f) := by
    linear_combination (-f) * hk'
  rw [e1, gauge_op G m m₁ L dd D h₁ e hF c hc p k O' hOp,
    h₁.glue k p.1 p'.1 O' (le_inf (hOp.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) (hOp'.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p')))]
  conv_rhs => rw [ef, gauge_op G m m₁ L dd D h₁ e hF c hc p' k O' hOp']
  linear_combination (-(op G dd h₁.Θ h₁.u (h₁.d p'.1) (h₁.p p'.1) (h₁.p' p'.1) k O'
    (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f))) * hk

end General

theorem gauge_acts {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (hF : ∀ a, IsField ⊤ (dd a))
    (c : R) (hc : 2 * c = 1) (k : ℕ) (σ σ' : SecM m₁ L k) (ρ ρ' : SecM m L k)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val)
    (hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val)
    (hA : h₁.Acts k σ σ') (p : h₁.J × (Fin 2 → L.ι)) :
    rsT (ρ'.f fun _ => p.2 0) (W m h₁ p) = op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k
      (W m h₁ p) (rsT (ρ.f fun _ => p.2 0) (W m h₁ p)) := by
  have c1 := gauge_chart G m m₁ L dd D h₁ e hL he k σ ρ hρ p
  have c2 := gauge_chart G m m₁ L dd D h₁ e hL he k σ' ρ' hρ' p
  have hU : rsT (gU m h₁ e p).val (W m h₁ p) = (gU m h₁ e p).val := GlobalTheory.KS.rsT_self _
  rw [c1, c2, ← hU, gauge_op G m m₁ L dd D h₁ e hF c hc p k _ le_rfl, hU]
  congr 1
  have hWc : h₁.W p.1 ≤ (LB.LinComb L (K := Fin 1) (fun _ => m₁) fun _ => (k : ℤ)).U (fun _ => h₁.j p.1) :=
    GlobalTheory.Heat.Glue.le_wchart _ (h₁.le p.1)
  rw [← GlobalTheory.KS.rsT_rsT hWc (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p) (σ'.f fun _ => h₁.j p.1), hA p.1,
    op_rsT G dd hF _ _ _ _ _ k (h₁.lift p.1).1 le_rfl (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p),
    GlobalTheory.KS.rsT_rsT hWc (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)]

theorem gauge_basic {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) {n : ℕ} (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left)
    (hinv : ∀ a, IsInv Y.H (v a) (dd a)) (D : R → R)
    (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D)
    (hB₁ : ∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧
      ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
        IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f))
    (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X)
    (hwe : ∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens),
      Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j →
        IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))
    (c : R) (p : h₁.J × (Fin 2 → Q.P.L.ι)) :
    (∃ V : Q.P.A.left.Opens, W Y.q.left h₁ p = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (gP Y.q.left h₁ e c p) ∧
      IsWt Y 0 _ (gP' Y.q.left h₁ e c p) ∧
      ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ W Y.q.left h₁ p → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
        IsWt Y α (Y.q.left ⁻¹ᵁ V) (gD Y.q.left h₁ e p _ f) := by
  obtain ⟨τ, hτ⟩ := trans_factor Q oa Y x
  obtain ⟨⟨V₁, hV₁⟩, hp₁, hp₁', hd₁⟩ := hB₁ p.1
  let Vp : Q.P.A.left.Opens := V₁ ⊓ (Q.P.L.U (p.2 0) ⊓ τ ⁻¹ᵁ Q.P.L.U (p.2 1))
  have hm₁ : ∀ y, ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) y = τ (Y.q.left y) := fun y => by
    rw [hτ, Scheme.Hom.comp_apply]
  have hWp : W Y.q.left h₁ p = Y.q.left ⁻¹ᵁ Vp := by
    refine TopologicalSpace.Opens.ext (Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩)
    · have h1 : y ∈ Y.q.left ⁻¹ᵁ V₁ := hV₁ ▸ hy.1
      have h2 := Set.mem_iInter.1 hy.2
      refine ⟨h1, h2 0, ?_⟩
      show τ (Y.q.left y) ∈ Q.P.L.U (p.2 1)
      rw [← hm₁]; exact h2 1
    · have h1 : y ∈ h₁.W p.1 := hV₁ ▸ hy.1
      refine ⟨h1, Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨hy.2.1, ?_⟩)⟩
      show ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) y ∈ Q.P.L.U (p.2 1)
      rw [hm₁]; exact hy.2.2
  have tr : ∀ (α : Q.X) (W₀ : Y.H.left.Opens), W₀ = Y.q.left ⁻¹ᵁ Vp → ∀ f : Γ(Y.H.left, W₀),
      IsWt Y α (Y.q.left ⁻¹ᵁ Vp) (rsT f (Y.q.left ⁻¹ᵁ Vp)) → IsWt Y α W₀ f := by
    rintro α W₀ rfl f h
    rwa [GlobalTheory.KS.rsT_self] at h
  have hU : IsWt Y β (W Y.q.left h₁ p) (gU Y.q.left h₁ e p).val :=
    tr β _ hWp _ (gauge_wt Q oa Y dd D x h₁ e β hwe p Vp hWp.ge)
  have hdW : ∀ α f, IsWt Y α (W Y.q.left h₁ p) f → IsWt Y α (W Y.q.left h₁ p) (h₁.d p.1 (W Y.q.left h₁ p) f) := by
    have hle : Y.q.left ⁻¹ᵁ Vp ≤ h₁.W p.1 := hWp ▸ heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p
    rw [hWp]
    exact fun α => hd₁ α Vp hle
  have hinvU : (gU Y.q.left h₁ e p).val * (gU Y.q.left h₁ e p)⁻¹.val = 1 := Units.mul_inv _
  have hL0 : ∀ a, IsWt Y 0 (W Y.q.left h₁ p) (gL Y.q.left h₁ e a p) := fun a =>
    GlobalTheory.Heat.WtPres.isWt_div (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) β _ _ hU) hU hinvU
  have hE0 : IsWt Y 0 (W Y.q.left h₁ p) (gE Y.q.left h₁ e p) :=
    GlobalTheory.Heat.WtPres.isWt_div (hdW β _ hU) hU hinvU
  have hY0 : ∀ a, IsWt Y 0 (W Y.q.left h₁ p) (gY Y.q.left h₁ e a p) := fun a =>
    GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ => GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 b)
  refine ⟨⟨Vp, hWp⟩, ?_, ?_, fun α V hV f hf => ?_⟩
  · refine GlobalTheory.Heat.WtAlg.isWt_sub (GlobalTheory.Heat.WtAlg.isWt_sub
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p) hp₁) hE0) ?_
    refine GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) ?_
    exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ =>
      GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 a)) (hL0 b)
  · refine GlobalTheory.Heat.WtAlg.isWt_sub (GlobalTheory.Heat.WtAlg.isWt_add
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p) hp₁') ?_) ?_
    · refine GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) ?_
      exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ =>
        GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _)
          (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) 0 _ _ (hL0 b))
    · exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ =>
        GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 a)
  · show IsWt Y α _ (h₁.d p.1 _ f + ∑ a, rsT (gY Y.q.left h₁ e a p) _ * dd a _ f)
    exact GlobalTheory.Heat.WtAlg.isWt_add (hd₁ α V (hV.trans (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p)) f hf)
      (GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul
        (GlobalTheory.Heat.Adjust.isWt_rsT Y hV (hY0 a)) (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) α _ _ hf))

theorem exists_gauge_heat : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D), (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) → ∀ (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h₁.Θ ∧ h'.u = h₁.u ∧ ∀ (k : ℕ) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k) (ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val) → h₁.Acts k σ σ' → h'.Acts k ρ ρ' := by
  intro R _ _ _ Q O _ _ _ oa Y n v dd hinv D x h₁ hB₁ e β he hwe
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hF : ∀ a, IsField ⊤ (dd a) := fun a => (hinv a).1
  have hc : 2 * algebraMap ℚ R (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  refine ⟨⟨h₁.Θ, h₁.symm, h₁.u, h₁.J × (Fin 2 → Q.P.L.ι), W Y.q.left h₁, fun p => p.2 0,
    gD Y.q.left h₁ e, gP Y.q.left h₁ e (algebraMap ℚ R (1 / 2)), gP' Y.q.left h₁ e (algebraMap ℚ R (1 / 2)),
    gauge_cover Y.H _ _ Q.P.L dd _ h₁ hL, fun p => W_le_m Y.q.left h₁ p,
    gauge_lift Y.H _ _ Q.P.L dd _ h₁ e hF (fun a O' r => GlobalTheory.Heat.Adjust.inv_constFn Y.H (v a) (dd a) (hinv a) O' r),
    fun k p p' O' hO f => gauge_glue Y.H _ _ Q.P.L dd _ h₁ e hL he hF _ hc k p p' O' hO f⟩,
    gauge_basic Q oa Y v dd hinv _ x h₁ hB₁ e β hwe _, rfl, rfl, ?_⟩
  intro k σ σ' ρ ρ' hρ hρ' hA p
  exact gauge_acts Y.H _ _ Q.P.L dd _ h₁ e hL he hF _ hc k σ σ' ρ ρ' hρ hρ' hA p

end GlobalTheory.Heat.Gauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackUniformisingGroupSameGenericFib
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endU_genMap {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) : E.aA.left ≫ genMap U = genMap U ≫ E.aG.left := by
  have h1 : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK V)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have h1' : E.aA.left ≫ U.gen.inv.left = U.gen.inv.left ≫ ((Over.pullback (jK V)).map E.aG).left := by
    have := congrArg CommaMorphism.left h1
    simpa only [Over.comp_left] using this
  have h2 : ((Over.pullback (jK V)).map E.aG).left ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ E.aG.left :=
    pullback.lift_fst _ _ _
  unfold genMap
  rw [← Category.assoc, h1', Category.assoc, h2, Category.assoc]

theorem exists_ext : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (gm : A.A.left ⟶ H.left), IsGrpPullback A.A H (jK V ≫ ξ) gm → ∃ β : G.left ⟶ H.left, IsGrpPullback G H ξ β ∧ genMap U ≫ β = gm ∧ ∀ (E : EndU U.toUnifPre) (Fm : H ⟶ H), E.aA.left ≫ gm = gm ≫ Fm.left → E.aG.left ≫ β = β ≫ Fm.left := by
  intro B H _ _ hH V _ _ _ hV G _ _ hG D A U ξ gm hgm
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hV
  haveI := hN
  haveI := hIC
  have gpA : IsGrpPullback A.A G (jK V) (genMap U) := by
    have := U.gen_hom
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr
      (Category.id_comp _) rfl
  have : IsMonHom (Iso.refl H).hom := by show IsMonHom (𝟙 H); infer_instance
  have hHH : IsGrpPullback H H (𝟙 B) (𝟙 H.left) := isGrpPullback_of_iso (Iso.refl H)
  obtain ⟨β, hβ, hβg⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 B) H H (𝟙 _) hH hHH G hG ξ (jK V ≫ ξ)
    (Category.comp_id _) A.A (genMap U) gm gpA hgm
  have hβg' : genMap U ≫ β = gm := by simpa using hβg
  refine ⟨β, hβ, hβg', ?_⟩
  intro E Fm hE
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSchemeTheoreticallyDominant (genMap U) := .of_isPullback gpA.1.flip
  have key := endU_genMap U E
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant H.hom ?_ (genMap U) ?_
  · rw [Category.assoc, Category.assoc, Over.w Fm, hβ.1.w, ← Category.assoc, Over.w E.aG]
  · rw [← Category.assoc, ← key, Category.assoc, hβg', hE, ← Category.assoc, hβg']

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_isPullDeg_comp_of_preimage {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hW : specOf i ⁻¹ᵁ p.W = ⊤) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ', hv⟩ := PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg'⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := PsiEvenPull.psi_pull q x (𝟙 _) z hJ' hJ''
      have ag : val (ψ'.psi (q.xe x)) g z J' = val (q.psiW.psi (q.xe x)) (𝟙 _ ≫ q.g) z J' :=
        ArcSpecialise.psiOn_agree ψ' q.psiW _ _ _ (by rw [hg', Category.id_comp, q.g_comm]) hJ'
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg', Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om q.w z J' J'' (𝟙 _ ≫ D''.xK x))⁻¹ * _ at v₂
      rw [ag, v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_isPullDeg_comp_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  intro R R' R'' _ _ _ _ _ _ i j D D' D'' p q e
  exact exists_isPullDeg_comp_of_preimage p q (by rw [e]; rfl)

end GlobalTheory.PullDegCompTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegIdSameCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivIso

theorem exists_isPullDeg_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ k, s k ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' iw s ε e' → ∃ hD : IsPullDeg (RingHom.id V) Q Q', (∀ y, e (hD.xe y) = e' y) ∧ (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (oQ.onB.act x)) := by
  intro E _ _ _ H D' l c L V _ _ _ Q _ oQ Q' _ oQ' iw I _ s ε e e' hs ⟨g, p, hg, hx, ha⟩ ⟨g', p', hg', hx', ha'⟩
  letI := H.starRing
  obtain ⟨q, q₁, q₂⟩ := GlobalTheory.PullDegTop.main.2.2.2 (RingHom.id_comp iw) p p' (fun y => L.gen (l.M' • y))
  have he : ∀ y : Q'.X, e (q.xe y) = e' y := fun y => (hx _).symm.trans ((q₂ y).trans (hx' y))
  obtain ⟨r, r₁, r₂⟩ := GlobalTheory.PullDegResc.main.2.1 g g' q s hs (fun y k => (l.M' : ℤ) * ε k (e y) (H.w0 • e y)) hg
    (fun x => (hg' x).trans (Finset.prod_congr rfl fun k _ => by rw [← he x]; rfl))
  refine ⟨r, fun y => (congrArg e (r₂ y)).trans (he y), fun x => (GlobalTheory.PullDegTop.main.2.1 r _ _).2 ?_⟩
  have r' : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫
      p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) = p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
    (congrArg (· ≫ _) r₁).trans q₁
  have pb : IsPullback (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) Q.P.A.hom L.D.P.A.hom (spMap iw) :=
    (pull_grp p).1
  have w : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫ Q.P.A.hom =
      Q'.P.A.hom ≫ spMap (RingHom.id V) := (pull_grp r).1.w
  have b : (oQ.onB.act x).left ≫ p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha x).trans (Category.assoc _ _ _).symm
  have b' : (oQ'.onB.act x).left ≫ p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha' x).trans (Category.assoc _ _ _).symm
  refine pb.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) r').trans (b'.trans (Eq.symm ?_)))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) b).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) r')))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (oQ'.onB.act x))).trans (Eq.symm ?_))))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w (oQ.onB.act x))).trans w)

end GlobalTheory.UCanon.DivIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullDegWhole

theorem exists_isPullDeg_top : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  intro R R' _ _ _ _ i D D' p ⟨ψ⟩
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme,
      g ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι = jK R' ≫ specOf i :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨{ p with W := ⊤, psiW := ψ, g := g, g_comm := hg, psi_pr := fun x => ?_ }, rfl, rfl, fun _ => rfl⟩
  obtain ⟨b, hb, hc⟩ := p.psi_pr x
  refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc _).trans (by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact GlobalTheory.ArcSpecialise.psiOn_agree p.psiW ψ _ _ _
      (by rw [Category.assoc, Category.assoc]; exact congrArg _ (p.g_comm.trans hg.symm)) hJ)⟩

end GlobalTheory.PullDegWhole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegrals
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem exists_isMix_of_arch : ArchInteg → ArchRecip →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  intro hI hR
  have key : ∀ m : ℕ, ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T := by
    intro m
    induction m with
    | zero => intro k _ Y q _; exact ⟨_, isMix_zero q⟩
    | succ m ih => exact _root_.GlobalTheory.MixHt.Step.isMix_succ hI hR m ih
  intro k _ Y q h m
  exact key m k Y q h

end GlobalTheory.MixHt
end

