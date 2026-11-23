module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesAffine
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.CechH1Span

theorem resG_appLE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {O O' : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (h : O' ≤ O)
    (r : Γ(X, U.1)) :
    resG t.G.left h ((t.G.hom.appLE U.1 O hO).hom r) = (t.G.hom.appLE U.1 O' (h.trans hO)).hom r := by
  show ((t.G.hom.appLE U.1 O hO) ≫ t.G.left.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]


set_option maxHeartbeats 1000000 in
theorem exists_dlog_add_coboundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) := by
  classical
  intro E _ _ _ H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj c hc
  let ρ : ∀ p : J × J, Γ(X, U.1) →+* Γ(t.G.left, W p.1 ⊓ W p.2) := fun p =>
    (t.G.hom.appLE U.1 (W p.1 ⊓ W p.2) (inf_le_left.trans (hWU p.1))).hom
  letI inst : ∀ p : J × J, Module Γ(X, U.1) Γ(t.G.left, W p.1 ⊓ W p.2) := fun p => Module.compHom _ (ρ p)
  have smul_apply : ∀ (r : Γ(X, U.1)) (x : ∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) (p : J × J),
      (r • x) p = ρ p r * x p := fun _ _ _ => rfl
  let Z : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    { carrier := {x | ∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (x (i, i')) +
          resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
            (x (i', i'')) =
          resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
            (x (i, i''))}
      add_mem' := by
        intro a b ha hb i i' i''
        simp only [Pi.add_apply, map_add (f := _)]
        rw [← ha i i' i'', ← hb i i' i'']
        abel
      zero_mem' := by
        intro i i' i''
        simp
      smul_mem' := by
        intro r x hx i i' i''
        simp only [smul_apply, map_mul]
        rw [← hx i i' i'']
        simp only [ρ, resG_appLE]
        ring }
  let Bd : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    { carrier := {x | ∃ h : ∀ i : J, Γ(t.G.left, W i), ∀ i i',
          x (i, i') = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i')}
      add_mem' := by
        rintro a b ⟨h1, e1⟩ ⟨h2, e2⟩
        refine ⟨h1 + h2, fun i i' => ?_⟩
        simp only [Pi.add_apply, map_add (f := _), e1, e2]
        ring
      zero_mem' := ⟨0, fun i i' => by simp⟩
      smul_mem' := by
        rintro r x ⟨h1, e1⟩
        refine ⟨fun i => (t.G.hom.appLE U.1 (W i) (hWU i)).hom r * h1 i, fun i i' => ?_⟩
        simp only [smul_apply, e1, map_mul, resG_appLE, ρ]
        ring }
  let κ : Fin n → (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) := fun b p =>
    δ b (W p.1 ⊓ W p.2) (resG t.G.left (inf_le_inf (hj p.1) (hj p.2)) (t.PP.L.g (j p.1) (j p.2)).val) *
      resG t.G.left (inf_le_inf (hj p.1) (hj p.2)) (t.PP.L.g (j p.1) (j p.2))⁻¹.val
  let S : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    Bd ⊔ Submodule.span Γ(X, U.1) (Set.range κ)
  let S' : Submodule Γ(X, U.1) Z := S.comap Z.subtype
  obtain ⟨N, e, he, hAe⟩ := _root_.GlobalTheory.CechFin.cech_h1_finite E H X t hP hA U J W hWa hcov hWU
  let ek : Fin N → Z := fun k => ⟨fun p => e k p.1 p.2, he k⟩
  have hspan : Submodule.span Γ(X, U.1) (Set.range fun k => S'.mkQ (ek k)) = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := S'.mkQ_surjective q
    obtain ⟨r, h, hz⟩ := hAe (fun i i' => z.1 (i, i')) (z.2)
    have hmem : z - ∑ k, r k • ek k ∈ S' := by
      refine Submodule.mem_sup_left ⟨h, fun i i' => ?_⟩
      change z.1 (i, i') - (∑ k, r k • ek k).1 (i, i') = _
      rw [Submodule.coe_sum, Finset.sum_apply, hz i i']
      simp only [Submodule.coe_smul, smul_apply, ρ]
      exact add_sub_cancel_right _ _
    have : S'.mkQ z = ∑ k, r k • S'.mkQ (ek k) := by
      have h0 : S'.mkQ (z - ∑ k, r k • ek k) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum] at h0
      simp only [map_smul] at h0
      exact sub_eq_zero.1 h0
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI : Module.Finite Γ(X, U.1) (Z ⧸ S') := ⟨⟨Finset.univ.image fun k => S'.mkQ (ek k), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hspan⟩⟩
  have hbot := GlobalTheory.submodule_eq_top_of_sup_maximal_smul_eq_top Γ(X, U.1) (Z ⧸ S') ⊥ (fun m hm => by
    rw [bot_sup_eq]
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := S'.mkQ_surjective q
    obtain ⟨θ, h, N', r, e', hr, he', hz⟩ :=
      _root_.GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod E H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj m hm
        (fun i i' => z.1 (i, i')) z.2
    let ek' : Fin N' → Z := fun k => ⟨fun p => e' k p.1 p.2, he' k⟩
    have hmem : z - ∑ k, r k • ek' k ∈ S' := by
      have hw : ∑ b, θ b • κ b ∈ Submodule.span Γ(X, U.1) (Set.range κ) :=
        Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
      have hy : (fun p : J × J => resG t.G.left (inf_le_left : W p.1 ⊓ W p.2 ≤ W p.1) (h p.1) -
          resG t.G.left (inf_le_right : W p.1 ⊓ W p.2 ≤ W p.2) (h p.2)) ∈ Bd := ⟨h, fun i i' => rfl⟩
      change (z - ∑ k, r k • ek' k : Z).1 ∈ S
      refine Submodule.mem_sup.2 ⟨_, hy, _, hw, ?_⟩
      funext p
      obtain ⟨i, i'⟩ := p
      change _ = z.1 (i, i') - (∑ k, r k • ek' k).1 (i, i')
      rw [Submodule.coe_sum, Finset.sum_apply, Pi.add_apply, Finset.sum_apply, hz i i']
      simp only [Submodule.coe_smul, smul_apply, ρ, κ]
      exact (add_sub_cancel_right _ _).symm
    have hq : S'.mkQ z = ∑ k, r k • S'.mkQ (ek' k) := by
      have h0 : S'.mkQ (z - ∑ k, r k • ek' k) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum] at h0
      simp only [map_smul] at h0
      exact sub_eq_zero.1 h0
    rw [hq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hr k) Submodule.mem_top)
  let cz : Z := ⟨fun p => c p.1 p.2, hc⟩
  have hcz : S'.mkQ cz = 0 := by
    have : S'.mkQ cz ∈ (⊥ : Submodule Γ(X, U.1) (Z ⧸ S')) := hbot ▸ Submodule.mem_top
    exact (Submodule.mem_bot _).1 this
  have hcS0 : cz ∈ S' := (Submodule.Quotient.mk_eq_zero S').1 hcz
  have hcS : cz.1 ∈ S := hcS0
  obtain ⟨y, ⟨h, hy⟩, w, hw, hyw⟩ := Submodule.mem_sup.1 hcS
  obtain ⟨θ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hw
  refine ⟨θ, h, fun i i' => ?_⟩
  have k := congrFun hyw (i, i')
  change _ = c i i' at k
  rw [← k, Pi.add_apply, hy i i', Finset.sum_apply]
  simp only [smul_apply, ρ, κ]

end GlobalTheory.CechH1Span
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreLiftCommTranslationSectionRatios
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

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.HeatRatioW.exists_acts {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) {O : Type} [CommRing O]
    [StarRing O] [Module O Dd.toPre.X] {oa : Dd.toPre.OAct O} (Y : Ray oa) {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left) (hv : ∀ a, IsInv Y.H (v a) (dd a))
    (inst : Algebra ℤ R) (D : @Derivation ℤ R R _ _ _ inst _ _) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D)
    (hb : IsBasic Y h) (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) : ∃ σ', TActs Y h k α σ σ' := by
  obtain rfl : inst = Ring.toIntAlgebra R := Subsingleton.elim _ _
  exact heat_acts_on_terms R Dd O oa Y n v dd hv D h hb k α σ


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.HeatRatioW.dl_comm_transl_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (N : ℕ), 1 ≤ N → ∀ (σ σ' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, U)), (∀ z ∈ U, ∀ J, Good P.D.toPre.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J) → dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) = pbT T₀ (dl U f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc y T₀ hT₀ hT₀' N hN σ σ' U f hf
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have hr : GlobalTheory.HeatRatio.IsRatio P.D.toPre σ σ' U f := hf
  have hN2 : 1 ≤ 2 * N := by omega
  obtain ⟨ρ₁, ρ₁', hr2⟩ := GlobalTheory.HeatRatio.isRatio_square _ P.D.toPre N σ σ' U f hN hr
  have HA := fun (k' : ℕ) (α : P.D.toPre.X) (s : P.D.toPre.SecB k' α) =>
    GlobalTheory.HeatRatioW.exists_acts P.D Y v' dd hdd _ D h hb k' α s
  obtain ⟨σp, a1⟩ := HA N 0 σ
  obtain ⟨σp', a2⟩ := HA N 0 σ'
  obtain ⟨ρp, a3⟩ := HA (2 * N) 0 ρ₁
  obtain ⟨ρp', a4⟩ := HA (2 * N) 0 ρ₁'
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.HeatRatio.exists_isRem _ P.D.toPre N 0 σ σ' σp σp' U f hr
  obtain ⟨g₂, hg₂⟩ := GlobalTheory.HeatRatio.exists_isRem _ P.D.toPre (2 * N) 0 ρ₁ ρ₁' ρp ρp' U f hr2
  have e1 := GlobalTheory.HeatRatio.Closed.closed_fibre_rem_indep E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc N (2 * N) hN hN2 0 0 σ σ' σp σp' ρ₁ ρ₁' ρp ρp' U f g₁ g₂ hr hr2 a1 a2 a3 a4 hg₁ hg₂
  obtain ⟨β₁, s, s', sp, sp', b1, b2, b3, b4⟩ := GlobalTheory.T.translation_carries_ratioDatum_remainder E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq
    h hb hdef y N hN σ σ' σp σp' U f g₁ hr a1 a2 hg₁
  obtain ⟨β₂, r, r', rp, rp', c1, c2, c3, c4⟩ := GlobalTheory.T.translation_carries_ratioDatum_remainder E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq
    h hb hdef y (2 * N) hN2 ρ₁ ρ₁' ρp ρp' U f g₂ hr2 a3 a4 hg₂
  have e2 := GlobalTheory.HeatRatio.Closed.closed_fibre_rem_indep E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hΘ ρ hρ A₀ grp m₀ hpb dl hdl
    hdesc N (2 * N) hN hN2 β₁ β₂ s s' sp sp' r r' rp rp' _ _ _ _ b1 c1 b2 b3 c2 c3 b4 c4

  set T := (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left with hTdef
  have hle : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ T₀ ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := by
    intro x hx
    have e : (T₀ ≫ m₀) x = (m₀ ≫ T) x := by rw [hT₀]
    show m₀ (T₀ x) ∈ U
    have e' : m₀ (T₀ x) = T (m₀ x) := by simpa using e
    rw [e']; exact hx
  have key : ∀ (φ ψ : A₀.left ⟶ P.D.toPre.P.A.left), φ = ψ → ∀ (h1 : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ U)
      (h2 : m₀ ⁻¹ᵁ (T ⁻¹ᵁ U) ≤ ψ ⁻¹ᵁ U), φ.appLE U _ h1 = ψ.appLE U _ h2 := by
    rintro φ _ rfl _ _; rfl
  have L5 : ∀ g : Γ(P.D.toPre.P.A.left, U), (m₀.app (T ⁻¹ᵁ U)).hom ((T.app U).hom g) =
      (T₀.appLE (m₀ ⁻¹ᵁ U) (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) hle).hom ((m₀.app U).hom g) := by
    intro g
    have c1 := Scheme.Hom.comp_appLE m₀ T U (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) le_rfl
    have c2 := Scheme.Hom.comp_appLE T₀ m₀ U (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) (le_trans hle le_rfl)
    have c3 := key _ _ hT₀ (le_trans hle le_rfl) le_rfl
    have := congrArg (fun φ => φ.hom g) (c2.symm.trans (c3.trans c1))
    simpa [Scheme.Hom.app_eq_appLE] using this.symm
  rw [pbT, dite_eq_left hle]
  set φ := (T₀.appLE (m₀ ⁻¹ᵁ U) (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) hle).hom
  rw [L5, L5] at e2
  have h1 : (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f = (m₀.app U).hom g₂ - (m₀.app U).hom g₁ := by
    push_cast at e1; linear_combination e1
  have h2 : (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U))) * dl _ ((T.app U).hom f) =
      φ ((m₀.app U).hom g₂) - φ ((m₀.app U).hom g₁) := by
    push_cast at e2; linear_combination e2
  rw [← map_sub, ← h1, map_mul, map_mul, map_ofNat, map_natCast] at h2
  have hu : IsUnit (2 * N : Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U))) := by
    let ψ : k →+* Γ(A₀.left, m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) :=
      (A₀.hom.appLE ⊤ (m₀ ⁻¹ᵁ (T ⁻¹ᵁ U)) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have hk : IsUnit (2 * N : k) := by
      refine IsUnit.mk0 _ ?_
      exact_mod_cast (by omega : 2 * N ≠ 0)
    have := hk.map ψ
    rwa [map_mul, map_ofNat, map_natCast] at this
  exact hu.mul_left_cancel h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepEqOfCongMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.DeepSame

theorem deep_eq_of_congMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') → (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) → ∀ (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → IsProjOver D.X.M.s → ∀ (ct₀ : UCTrait D.X p z₂) (yy₀ : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct₀.T.P.D.toPre.X), UIsLabW D.X w₂ ct₀ yy₀ → ∀ (a a' : D.X.S.Gam) (ν ν' : ct₀.T.P.D.toPre.X), yy₀ a = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → ∀ κ, f a κ = f a' κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz f t hf hsum w₁ w₂ htie hproj ct₀ yy₀ hyy₀ a a' ν ν' ha ha' hcong κ
  obtain ⟨U₁, hU₁, hct⟩ := GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X₁ p
  have hU : ((D.q ⁻¹ᵁ U₁ : D.X.M.Z.Opens) : Set D.X.M.Z).Nonempty :=
    GlobalTheory.Poinc.FinPts.preimage_nonempty D.gen hU₁
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := by
    have := D.X.normal
    intro x
    exact ⟨inferInstance, inferInstance⟩
  have hfa : f a κ ∈ D.X.M.O z₂ := hf a κ z₂ hz
  have hfa' : f a' κ ∈ D.X.M.O z₂ := hf a' κ z₂ hz
  have hb : f a κ - f a' κ ∈ D.X.M.O (ct₀.y (cPt p)) := by
    rw [ct₀.cen]; exact sub_mem hfa hfa'
  have key := GlobalTheory.Poinc.eq_zero_of_val_cen_eq_zero D.X.o₁ D.X.Ω₁ D.X.M hN (D.q ⁻¹ᵁ U₁) hU p ct₀.y
    (f a κ - f a' κ) hb ?_
  · exact sub_eq_zero.1 key
  intro y' hy'
  obtain ⟨hcen, hrange⟩ := hy'
  rw [ct₀.cen] at hcen
  have hr₁ : Set.range (gPt p ≫ (y' ≫ D.q)) ⊆ (U₁ : Set X₁.M.Z) := by
    rintro _ ⟨w, rfl⟩
    exact hrange ⟨w, rfl⟩
  obtain ⟨ct', hct'⟩ := hct (y' ≫ D.q) hr₁
  have hz₁ : (y' ≫ D.q) (cPt p) = z₁ := by rw [← hz, ← hcen]; rfl
  let ct₁ : UCTrait X₁ p z₁ :=
    { y := y' ≫ D.q, cen := hz₁, T := ct'.T, ι := ct'.ι, int := ct'.int,
      comm := by have hc := ct'.comm; rw [hct'] at hc; exact hc }
  obtain ⟨yy₁, hyy₁⟩ := _root_.GlobalTheory.UPoinc.exists_uIsLabW E H Dw hpq l Xo cf C X₁ w₁ p z₁ ct₁
  obtain ⟨yy, hyy, hcomp⟩ := _root_.GlobalTheory.UPoinc.ULift.labels_lift E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct₁ yy₁ hyy₁ y' rfl
  let ct₂ : UCTrait D.X p z₂ := { D.lift ct₁ y' rfl with cen := hcen }
  have hyy₂ : UIsLabW D.X w₂ ct₂ yy := hyy
  obtain ⟨e, he⟩ := _root_.GlobalTheory.UPoinc.exists_linearEquiv_labelled_of_uIsLabW E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ ct₀ ct₂ yy₀ yy hyy₀ hyy₂
  have h1 := he a ν ha
  have h2 := he a' ν' ha'
  obtain ⟨w, hw⟩ := hcong
  have hc : CongMod D.m (e ν) (e ν') := ⟨e w, by rw [hw, map_add (f := _), map_nsmul]⟩
  have hfin : ∀ δ : ℝ, 0 < δ → ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ ≤ 2 * δ := by
    intro δ hδ
    obtain ⟨S₀, hS₀⟩ := hsum ct₁ yy₁ hyy₁.uIsLab y' rfl hcen yy hyy.uIsLab hcomp a (e ν) κ h1 δ hδ
    obtain ⟨S₀', hS₀'⟩ := hsum ct₁ yy₁ hyy₁.uIsLab y' rfl hcen yy hyy.uIsLab hcomp a' (e ν') κ h2 δ hδ
    let S := (S₀ ∪ S₀').filter (fun μ => CongMod D.m μ (e ν))
    have A := hS₀ S (fun μ hμ => (Finset.mem_filter.1 hμ).2)
      (fun μ hμ hc' => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hc'⟩)
    have B := hS₀' S
      (fun μ hμ => by
        obtain ⟨w₁', hw₁'⟩ := (Finset.mem_filter.1 hμ).2
        obtain ⟨w₂', hw₂'⟩ := hc
        exact ⟨w₁' + w₂', by rw [hw₁', hw₂', smul_add]; abel⟩)
      (fun μ hμ hc' => by
        refine Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, ?_⟩
        obtain ⟨w₁', hw₁'⟩ := hc'
        obtain ⟨w₂', hw₂'⟩ := hc
        exact ⟨w₁' - w₂', by rw [hw₁', hw₂', smul_sub]; abel⟩)
    calc ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖
        = ‖(D.X.M.val (gPt p ≫ y') (f a κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ) -
            (D.X.M.val (gPt p ≫ y') (f a' κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ)‖ := by congr 1; abel
      _ ≤ ‖D.X.M.val (gPt p ≫ y') (f a κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ‖ +
            ‖D.X.M.val (gPt p ≫ y') (f a' κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add A B
      _ = 2 * δ := by ring
  have hxx : D.X.M.val (gPt p ≫ y') (f a κ) = D.X.M.val (gPt p ≫ y') (f a' κ) := by
    by_contra hne
    have hpos : 0 < ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 hne)
    have := hfin (‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ / 4) (by positivity)
    linarith
  have hsp : ∀ w, (gPt p ≫ y') w ⤳ z₂ := GlobalTheory.ZH.RatModel.gPt_specializes hcen
  have hadd := GlobalTheory.ZH.RatModel.val_add hsp (sub_mem hfa hfa') hfa'
  rw [sub_add_cancel] at hadd
  rw [hadd] at hxx
  simpa using hxx

end GlobalTheory.UPoinc.DeepSame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfClassSumApprox
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GalLab

theorem eq_of_classSum_approx {X K : Type} [AddCommGroup X] [NormedAddCommGroup K] (m : ℕ) (τ : X → K) (ν ν' : X)
    (h : CongMod m ν ν') (u v : K)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset X, ∀ S : Finset X, (∀ μ ∈ S, CongMod m μ ν) →
      (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖u - ∑ μ ∈ S, τ μ‖ ≤ δ)
    (hv : ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset X, ∀ S : Finset X, (∀ μ ∈ S, CongMod m μ ν') →
      (∀ μ ∈ S₀, CongMod m μ ν' → μ ∈ S) → ‖v - ∑ μ ∈ S, τ μ‖ ≤ δ) : u = v := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ μ, CongMod m μ ν ↔ CongMod m μ ν' := fun μ =>
    ⟨fun ⟨x, hx⟩ => ⟨w + x, by rw [hx, hw, smul_add, add_assoc]⟩,
      fun ⟨x, hx⟩ => ⟨x - w, by rw [hx, hw, smul_sub]; abel⟩⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨S₀, h₀⟩ := hu (δ / 2) (half_pos hδ)
  obtain ⟨S₁, h₁⟩ := hv (δ / 2) (half_pos hδ)
  have a := h₀ ((S₀ ∪ S₁).filter fun μ => CongMod m μ ν) (fun μ hμ => (Finset.mem_filter.1 hμ).2)
    fun μ hμ hc => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hc⟩
  have b := h₁ ((S₀ ∪ S₁).filter fun μ => CongMod m μ ν) (fun μ hμ => (key μ).1 (Finset.mem_filter.1 hμ).2)
    fun μ hμ hc => Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, (key μ).2 hc⟩
  have c := norm_sub_le_norm_sub_add_norm_sub u (∑ μ ∈ (S₀ ∪ S₁).filter fun μ => CongMod m μ ν, τ μ) v
  rw [norm_sub_rev] at b
  linarith

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') → (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) → ∀ (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → IsProjOver D.X.M.s → ∀ (σ' : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), s ≫ D.q = D.q → (∀ (K : Type) [Field K] (y : Sp K ⟶ D.X.M.Z) (b : D.X.Ω₁), D.X.M.val (y ≫ s) b = D.X.M.val y (σ' b)) → s z₂ = z₂ → ∀ aσ : D.X.S.Gam ≃+ D.X.S.Gam, (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → UIsLab D.X (D.lift ct (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (aσ x)) → ∀ (ct₀ : UCTrait D.X p z₂) (yy₀ : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct₀.T.P.D.toPre.X), UIsLabW D.X w₂ ct₀ yy₀ → ∀ (a a' : D.X.S.Gam) (ν ν' : ct₀.T.P.D.toPre.X), yy₀ (aσ a) = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → ∀ κ, σ' (f a κ) = f a' κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz f t hf hsum w₁ w₂ htie hproj σ' s hs hval hsz aσ haσ ct₀ yy₀ hl₀
    a a' ν ν' ha ha' hνν' κ
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z :=
    fun x => ⟨D.X.normal.isDomain_stalk x, D.X.normal.isIntegrallyClosed_stalk x⟩
  have hσ : σ' (f a κ) ∈ D.X.M.O z₂ := by
    letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ :=
      ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
    have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ x =
      algebraMap X₁.Ω₁ D.X.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
    let φ : D.X.Ω₁ →ₐ[X₁.M.Z.presheaf.stalk z₁] D.X.Ω₁ :=
      { (σ' : D.X.Ω₁ →+* D.X.Ω₁) with commutes' := fun x => σ'.commutes (X₁.M.stalkHom z₁ x) }
    exact FinPts.mem_O_of_isIntegral hN D.gen halg
      ((FinPts.isIntegral_of_mem_O D.fin D.gen halg (hf a κ)).map φ) hz
  have hf' : f a' κ ∈ D.X.M.O z₂ := hf a' κ z₂ hz
  obtain ⟨U₁, hU₁, hct⟩ := GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X₁ p
  have hc₀ := ct₀.cen
  rw [← sub_eq_zero]
  refine eq_zero_of_val_cen_eq_zero _ _ D.X.M hN (D.q ⁻¹ᵁ U₁) (FinPts.preimage_nonempty D.gen hU₁) p ct₀.y _
    (by rw [hc₀]; exact sub_mem hσ hf') fun y hy => ?_
  obtain ⟨hy, hyU⟩ := hy
  rw [hc₀] at hy
  obtain ⟨ct₁, hct₁⟩ := hct (y ≫ D.q) (by
    rintro _ ⟨w, rfl⟩
    exact hyU ⟨w, rfl⟩)
  have hz₁ : (y ≫ D.q) (cPt p) = z₁ := by rw [← hz, ← hy]; rfl
  let ct : UCTrait X₁ p z₁ := { ct₁ with cen := ct₁.cen.trans hz₁ }
  have h : y ≫ D.q = ct.y := hct₁.symm
  have h' : (y ≫ s) ≫ D.q = ct.y := by rw [Category.assoc, hs, h]
  have hys : (y ≫ s) (cPt p) = z₂ := by
    show s (y (cPt p)) = z₂
    rw [hy, hsz]
  obtain ⟨yy₁, hl₁⟩ := _root_.GlobalTheory.UPoinc.exists_uIsLabW E H Dw hpq l Xo cf C X₁ w₁ p z₁ ct
  obtain ⟨yy, hl, hco⟩ := _root_.GlobalTheory.UPoinc.ULift.labels_lift E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct yy₁ hl₁ y h
  obtain ⟨yy', hl', hco'⟩ := _root_.GlobalTheory.UPoinc.ULift.labels_lift E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct yy₁ hl₁ (y ≫ s) h'
  have hyy := haσ ct yy₁ hl₁.uIsLab y h h' yy yy' hl.uIsLab hco hl'.uIsLab hco'
  let ct₂ : UCTrait D.X p z₂ := { D.lift ct y h with cen := hy }
  obtain ⟨d, hd⟩ := exists_linearEquiv_labelled_of_uIsLabW E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ ct₀ ct₂ yy₀ yy
    hl₀ hl
  have hdν : CongMod D.m (d ν) (d ν') := by
    obtain ⟨w, hw⟩ := hνν'
    exact ⟨d w, by rw [hw, map_add (f := _), map_nsmul]⟩
  have e := eq_of_classSum_approx D.m (fun μ => t ct yy₁ μ κ) _ _ hdν _ _
    (hsum ct yy₁ hl₁.uIsLab (y ≫ s) h' hys yy' hl'.uIsLab hco' a (d ν) κ ((hyy a).trans (hd _ _ ha)))
    (hsum ct yy₁ hl₁.uIsLab y h hy yy hl.uIsLab hco a' (d ν') κ (hd _ _ ha'))
  rw [← Category.assoc, hval] at e
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ z₂ := RatModel.gPt_specializes hy
  have e' := map_sub (RatModel.valHomOf _ z₂ hsp) ⟨_, hσ⟩ ⟨_, hf'⟩
  exact e'.trans (sub_eq_zero.2 e)

end GlobalTheory.UPoinc.GalLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameOffClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


set_option maxHeartbeats 4000000 in
theorem exists_carried_frame_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  have hβc : IsClosedMap β.base := by
    haveI : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
    haveI : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip inferInstance
    exact β.isClosedMap
  obtain ⟨V, hyV, s, hs, hun, hcar⟩ := _root_.GlobalTheory.Mum.exists_carried_sec_off_closed R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
  obtain ⟨V', hyV', -, T, hT, htr⟩ := _root_.GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre _ _ β hβc U'.LG.L U'.LG.isLB V s hs y hyV hun
  refine ⟨V', hyV', T, hT, ?_⟩
  intro σ h bc hbc hP hPO
  refine (hcar σ).elim fun h₀ hc => hc.elim fun bc₀ hc => ?_
  refine hc.2.elim fun hP₀ hc' => ?_
  have hF₀ := htr _ _ hc'.2
  have e : bc₀.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := hc.1.trans hbc.symm
  have s₁ := Classical.choose_spec hP.lg
  have s₀ := Classical.choose_spec hP₀.lg
  refine s₁.2.elim fun he₁ m₁ => s₀.2.elim fun he₀ m₀ => ?_
  have hg := GlobalTheory.T.uniformisationBundle_rigidLinearisations_same_localUnits R' D' A' G' hS' U' (specOf (Gal.hom σ)) _ _ e he₀ he₁ _ _ s₀.1 s₁.1 m₀.1 m₁.1
  intro z j k hz hfz hzk hfzj
  have h1 := hF₀ z j k hz (by rw [e]; exact hfz) hzk (by rw [e]; exact hfzj)
  rw [hg z j k hzk (by rw [e]; exact hfzj)] at h1
  rw [e] at h1
  exact h1

end GlobalTheory.Mum
end

