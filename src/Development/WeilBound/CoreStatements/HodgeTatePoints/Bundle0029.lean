module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0018
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0028
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0026
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsBialgHom
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Twpol

open Coalgebra WithConv

section Level

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A]
  {J : Type} (x : J → A →ₐ[O] O)

abbrev fm (a : J) : CartierDual O A := toConv (x a).toLinearMap

theorem sep_two (sep : ∀ f g : A, (∀ a, x a f = x a g) → f = g) (s t : A ⊗[O] A)
    (h : ∀ a b, CartierDual.pair O A A (fm x a ⊗ₜ fm x b) s = CartierDual.pair O A A (fm x a ⊗ₜ fm x b) t) :
    s = t := by
  have hr : ∀ (φ ψ : CartierDual O A) (s : A ⊗[O] A),
      φ (TensorProduct.rid O A (LinearMap.lTensor A ψ.ofConv s)) = CartierDual.pair O A A (φ ⊗ₜ ψ) s := by
    intro φ ψ s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp [mul_comm]
  have hl : ∀ (φ ψ : CartierDual O A) (s : A ⊗[O] A),
      ψ (TensorProduct.lid O A (LinearMap.rTensor A φ.ofConv s)) = CartierDual.pair O A A (φ ⊗ₜ ψ) s := by
    intro φ ψ s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp
  refine CartierDual.tensor_eq_of_forall_pair fun φ ψ => ?_
  rw [← hl, ← hl]
  refine congrArg _ (sep _ _ fun b => ?_)
  refine (hl φ (fm x b) s).trans (Eq.trans ?_ (hl φ (fm x b) t).symm)
  rw [← hr, ← hr]
  refine congrArg _ (sep _ _ fun a => ?_)
  exact (hr (fm x a) (fm x b) s).trans ((h a b).trans (hr (fm x a) (fm x b) t).symm)

theorem exists_bialgHom [AddCommGroup J] (sep : ∀ f g : A, (∀ a, x a f = x a g) → f = g)
    (h0 : fm x 0 = 1) (hadd : ∀ a b, fm x (a + b) = fm x a * fm x b)
    (l : CartierDual O A →ₗ[O] A) (u : J → A) (hl : ∀ a φ, x a (l φ) = φ (u a))
    (hu0 : ∀ b, x b (u 0) = 1) (hu0' : ∀ a, x 0 (u a) = 1)
    (hua : ∀ a a' b, x b (u (a + a')) = x b (u a) * x b (u a'))
    (hub : ∀ a b b', x (b + b') (u a) = x b (u a) * x b' (u a)) :
    ∃ lam : CartierDual O A →ₐc[O] A, ∀ φ, lam φ = l φ := by
  have hx0 : ∀ f, x 0 f = counit (R := O) f := fun f => congrArg (fun φ : CartierDual O A => φ f) h0
  have hxa : ∀ a b f, x (a + b) f = CartierDual.pair O A A (fm x a ⊗ₜ fm x b) (comul f) := fun a b f =>
    (congrArg (fun φ : CartierDual O A => φ f) (hadd a b)).trans (CartierDual.mul_apply _ _ _)
  have hone : u 0 = 1 := sep _ _ fun b => by rw [hu0, map_one]
  have hmul : ∀ a a', u (a + a') = u a * u a' := fun a a' => sep _ _ fun b => by rw [hua, map_mul]
  have hco : ∀ a, comul (R := O) (u a) = u a ⊗ₜ u a := fun a => sep_two x sep _ _ fun b b' => by
    rw [← hxa, hub, CartierDual.pair_tmul_tmul]; rfl
  let F : CartierDual O A →ₐ[O] A := AlgHom.ofLinearMap l
    (sep _ _ fun a => by rw [hl, map_one, CartierDual.one_apply, ← hx0, hu0'])
    (fun φ ψ => sep _ _ fun a => by
      rw [map_mul (x a), hl, hl, hl, CartierDual.mul_apply, hco, CartierDual.pair_tmul_tmul])
  have hF : ∀ φ, F φ = l φ := fun _ => rfl
  refine ⟨BialgHom.ofAlgHom F (AlgHom.ext fun φ => ?_) (AlgHom.ext fun φ => ?_), fun φ => rfl⟩
  · change counit (R := O) (l φ) = counit (R := O) φ
    rw [← hx0, hl, hone, CartierDual.counit_apply]
  · change Algebra.TensorProduct.map F F (comul (R := O) φ) = comul (R := O) (l φ)
    refine sep_two x sep _ _ fun a b => ?_
    rw [← hxa, hl, hmul, ← CartierDual.pair_comul_tmul]
    generalize comul (R := O) φ = s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
    | tmul φ ψ =>
      rw [Algebra.TensorProduct.map_tmul, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, ← hl, ← hl]
      rfl

end Level

theorem exists_linear {O A T J : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O (T → O))
    (e : A ≃ₐ[O] S) (q : J → T) (x : J → A →ₐ[O] O) (hx : ∀ a f, x a f = (e f).1 (q a))
    (s : T × T → O) (hs : s ∈ Submodule.span O {g | ∃ a ∈ S, ∃ b ∈ S, g = fun z : T × T => a z.1 * b z.2}) :
    ∃ (l : CartierDual O A →ₗ[O] A) (u : J → A),
      (∀ a φ, x a (l φ) = φ (u a)) ∧ ∀ a b, x b (u a) = s (q a, q b) := by
  induction hs using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f, hf, g, hg, rfl⟩ := hg
    refine ⟨(CartierDual.evalAt O A (e.symm ⟨g, hg⟩)).smulRight (e.symm ⟨f, hf⟩),
      fun a => f (q a) • e.symm ⟨g, hg⟩, fun a φ => ?_, fun a b => ?_⟩
    · rw [LinearMap.smulRight_apply, map_smul, map_smul, hx, AlgEquiv.apply_symm_apply, smul_eq_mul, smul_eq_mul,
        mul_comm]
      rfl
    · rw [map_smul, hx, AlgEquiv.apply_symm_apply, smul_eq_mul]
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | add s t _ _ hs ht =>
    obtain ⟨l, u, h1, h2⟩ := hs
    obtain ⟨l', u', h1', h2'⟩ := ht
    exact ⟨l + l', u + u', by simp [h1, h1'], by simp [h2, h2']⟩
  | smul c s _ hs =>
    obtain ⟨l, u, h1, h2⟩ := hs
    exact ⟨c • l, c • u, by simp [h1], by simp [h2]⟩

theorem tower_pol : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧ ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := exists_linear (X.A n) (e n) (lev p n) (fun a => (τ a).pt n)
      (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := exists_bialgHom (fun a => (τ a).pt n) (sep n)
      (by
        change toConv ((τ 0).pt n).toLinearMap = 1
        rw [map_zero]; rfl)
      (fun a b => by
        change toConv ((τ (a + b)).pt n).toLinearMap = _
        rw [map_add (f := _)]; rfl)
      l u h1 (fun b => by simp [h3]) (fun a => by rw [h3]; simp)
      (fun a a' b => by simp [h3, zpow_add]) (fun a b b' => by rw [h3, h3, h3]; simp [zpow_add])
    exact ⟨lam, u, fun a φ => by rw [hlam, h1], h3⟩
  choose lam u h1 h2 using key
  refine ⟨⟨lam, fun n => BialgHom.ext fun φ => sep n _ _ fun a => ?_⟩, fun a b n => ?_⟩
  · change (τ a).pt n (G.res n (lam (n + 1) φ)) = (τ a).pt n (lam n (CartierDual.map (G.mulP n) φ))
    rw [h1, hre.pt, hre.res, ← hre.pt, h1, CartierDual.map_apply]
    refine congrArg _ (sep _ _ _ fun b => ?_)
    rw [TateOver.pt_mulP, h2, h2, ← hζ n, ← zpow_natCast, ← zpow_mul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  · rw [← hre.pt, ← h2]
    refine congrArg _ (CartierDual.eq_of_forall_apply (R := O) fun φ => ?_)
    rw [apply_charElem, tateMap_pt]
    exact h1 n a φ

end PositivityTheory.HtPt.Twpol
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FreeOfFg
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

theorem free_of_fg {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
    (L : Submodule O Ω) (hL : L.FG) : Module.Free O L := by
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL
  haveI : Module.Flat O L := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have hx0 : (a : O) • (x : Ω) = 0 := by
      have := congrArg Subtype.val ha
      simpa [Submonoid.smul_def] using this
    rw [← algebraMap_smul C (a : O) (x : Ω), smul_eq_zero] at hx0
    rcases hx0 with h | h
    · exact absurd (hv.hom_inj (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero a)
    · exact (Submodule.mem_bot O).mpr (Subtype.ext (by simpa using h))
  exact Module.free_of_flat_of_isLocalRing

end PositivityTheory.HtPt.Gd
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GcField
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Gc

theorem test_field : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (p : ℕ) [Fact p.Prime] (𝔮 : Ideal A), 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 → ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : IsDomain O) (_ : Algebra O C) (v : Valuation C NNReal) (φ : A →+* O), v.Integers O ∧ v (p : C) < 1 ∧ IsAdicComplete (Ideal.span {(p : O)}) O ∧ Function.Injective φ ∧ ∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1 := by
  intro A _ _ _ _ _ p hp q hq h1 hpq
  obtain ⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra A R),
      IsLocalization.AtPrime R q ∧ IsDiscreteValuationRing R :=
    ⟨Localization.AtPrime q, inferInstance, inferInstance, inferInstance, inferInstance,
      dvr_of_height_one q h1⟩
  let K := FractionRing R
  have hAR : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R q.primeCompl_le_nonZeroDivisors
  haveI : CharZero R := charZero_of_injective_algebraMap hAR
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  have hpR : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff R q (p : A)).2 hpq
    rwa [map_natCast] at this
  obtain ⟨C, _, _, _, _, _, _, hC⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing R K p hpR
  obtain ⟨φ, hφ, hφ'⟩ := GlobalTheory.exists_isLocalHom_normIntegers hC
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  have hO := GlobalTheory.normIntegers_integers C
  have key : ∀ a : A, a ∈ q ↔
      NormedField.valuation (K := C) (algebraMap (GlobalTheory.normIntegers C) C (φ (algebraMap A R a))) < 1 := by
    intro a
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R q a, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, ← isUnit_map_iff φ, hO.isUnit_iff_valuation_eq_one]
    exact (hO.map_le_one _).lt_iff_ne.symm
  have hv : NormedField.valuation (K := C) (p : C) < 1 := by
    simpa only [map_natCast] using (key p).1 hpq
  refine ⟨C, GlobalTheory.normIntegers C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, NormedField.valuation, φ.comp (algebraMap A R), hO, hv, ?_, ?_, key⟩
  · apply GlobalTheory.NormIntegers.isAdicComplete_span_singleton hO
    exact_mod_cast hv
  · intro a b hab
    have : (φ (algebraMap A R a) : C) = (φ (algebraMap A R b) : C) := congrArg Subtype.val hab
    rw [hφ', hφ'] at this
    exact hAR (IsFractionRing.injective R K ((algebraMap K C).injective this))

end PositivityTheory.HtPt.Gc
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GdChartFin
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

theorem chart_comp_zero : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y :=
  chart_comp_zero_of @PositivityTheory.HtPt.Gc.test_div @PositivityTheory.HtPt.Gc.test_descend @PositivityTheory.HtPt.Gb.red_omHT_bc

end PositivityTheory.HtPt.Gd
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GiFree
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Gi

theorem free_on_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u → ∃ (ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)) (T : Submodule O (C ⊗[ℤ] La)) (e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C), (∀ (a : 𝓞 E) (x : La), ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧ T = Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x) ∧ IsFreeOn ρ T (fun i => 1 ⊗ₜ u i) ∧ (∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧ (∀ x, e x x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0) ∧ dualLat e T = T ∧ ∀ (a : 𝓞 E) x y, e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c La _ _ EF N u h
  classical
  have := h.free
  have := h.finite
  let ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La) :=
    (Module.End.baseChangeHom ℤ C La).toRingHom.comp (Module.toModuleEnd ℤ La)
  have hρ : ∀ (a : 𝓞 E) (s : C) (x : La), ρ a (s ⊗ₜ x) = s ⊗ₜ (a • x) := fun a s x => rfl
  let e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C := LinearMap.BilinForm.baseChange C EF
  have he : ∀ (s t : C) (x y : La), e (s ⊗ₜ x) (t ⊗ₜ y) = (EF x y : C) * (s * t) := fun s t x y => by
    simp only [e, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]
  have he1 : ∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C) := fun x y => by rw [he]; simp
  let T : Submodule O (C ⊗[ℤ] La) := Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x)
  have hT : ∀ x : La, (1 : C) ⊗ₜ[ℤ] x ∈ T := fun x => Submodule.subset_span ⟨x, rfl⟩
  let b := Module.Free.chooseBasis ℤ La
  let B := Algebra.TensorProduct.basis C b
  have hB : ∀ i, B i = 1 ⊗ₜ b i := fun i => Algebra.TensorProduct.basis_apply b i
  choose b' hb' using fun i => h.unimod.2 (b.coord i)
  have hrep : ∀ i y, e (1 ⊗ₜ b' i) y = B.repr y i := by
    intro i y
    have : e (1 ⊗ₜ b' i) = B.coord i := B.ext fun j => by
      rw [Module.Basis.coord_apply, B.repr_self, hB, he1, hb', Module.Basis.coord_apply, b.repr_self]
      simp only [Finsupp.single_apply]
      split_ifs <;> simp
    rw [this]; rfl
  have hskew : ∀ x y, EF x y = -EF y x := fun x y => by
    have := h.alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, h.alt] at this
    linarith
  have eskew : ∀ x y, e x y = -e y x := by
    intro x y
    induction x with
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
    | tmul s x =>
      induction y with
      | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
      | tmul t y => rw [he, he, hskew]; push_cast; ring
  have hTb : T = Submodule.span O (Set.range B) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      change (1 : C) ⊗ₜ[ℤ] x ∈ Submodule.span O (Set.range B)
      rw [← b.sum_repr x, tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [tmul_smul, ← hB]
      exact zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := B) i)) _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hB]; exact hT _
  have hsp : Submodule.span C (T : Set (C ⊗[ℤ] La)) = ⊤ := by
    rw [hTb, Submodule.span_span_of_tower, B.span_eq]
  let w : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → C ⊗[ℤ] La := fun q =>
    ρ (RingOfIntegers.basis E q.2) (1 ⊗ₜ u q.1)
  have hTw : T = Submodule.span O (Set.range w) := by
    apply le_antisymm
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : O)}) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [hTb]; exact Submodule.fg_span (Set.finite_range B)
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨x, rfl⟩
        obtain ⟨a, x', rfl⟩ := h.span x
        change (1 : C) ⊗ₜ[ℤ] _ ∈ Submodule.span O (Set.range w) ⊔ Ideal.span {(p : O)} • T
        rw [tmul_add]
        refine Submodule.add_mem_sup ?_ ?_
        · rw [tmul_sum]
          refine Submodule.sum_mem _ fun i _ => ?_
          rw [← (RingOfIntegers.basis E).sum_repr (a i), Finset.sum_smul, tmul_sum]
          refine Submodule.sum_mem _ fun k _ => ?_
          rw [smul_assoc, tmul_smul]
          exact zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := w) (i, k))) _
        · rw [tmul_smul, ← Nat.cast_smul_eq_nsmul O]
          exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hT _)
    · rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      exact hT _
  refine ⟨ρ, T, e, fun a x => hρ a 1 x, rfl, ⟨?_, hsp, hTw⟩, he1, fun x => ?_, fun y hy => ?_, ?_, fun a x y => ?_⟩
  · refine linearIndependent_of_top_le_span_of_card_eq_finrank (b := w) ?_ ?_
    · rw [← hsp, hTw, Submodule.span_span_of_tower]
    · rw [Module.finrank_baseChange, h.rank, Fintype.card_prod, Fintype.card_fin,
        ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  · have := eskew x x
    have h2 : (2 : C) * e x x = 0 := by linear_combination this
    simpa using h2
  · exact B.ext_elem fun i => by rw [← hrep, hy]; simp
  · apply le_antisymm
    · intro y hy
      rw [hTb, ← B.sum_repr y]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨o, ho⟩ := hy _ (hT (b' i))
      rw [← hrep, ← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩ x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        exact ⟨(EF x y : O), by rw [he1, map_intCast]⟩
      | zero => simp
      | add x x' _ _ hx hx' =>
        rw [map_add (f := _), LinearMap.add_apply]; exact Subring.add_mem _ hx hx'
      | smul o x _ hx =>
        rw [← algebraMap_smul C o x, map_smul, LinearMap.smul_apply, smul_eq_mul]
        exact Subring.mul_mem _ ⟨o, rfl⟩ hx
  · induction x with
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    | tmul s x =>
      induction y with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul t y => rw [hρ, hρ, he, he, h.adj]

end PositivityTheory.HtPt.Gi
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHtBc
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.HTBaseChange

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem valAt_spec_map {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (ψ : B →+* C)
    (y : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom ψ) ≫ y) ⊤ le_top s = ψ (valAt y ⊤ le_top s) := by
  rw [valAt_comp_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have := congrArg (fun φ => φ.hom (y.appTop.hom s)) h
  simp only [CommRingCat.comp_apply] at this
  exact this

abbrev qmap {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (N : ℕ) :
    R ⧸ Ideal.span {(N : R)} →+* R' ⧸ Ideal.span {(N : R')} :=
  Ideal.quotientMap (Ideal.span {(N : R')}) (algebraMap R R')
    (Ideal.span_le.2 (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span rfl))

end PositivityTheory.HtPt.Htat.HTBaseChange


open PositivityTheory.HtPt.Htat.HTBaseChange in
theorem PositivityTheory.HtPt.Htat.ht_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) → ∀ (L' : Type) [AddCommGroup L'] [Module R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →+ L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → Submodule.span R' (Set.range β) = ⊤ → ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (w' : Module.Dual R' L'), (∀ e, w' (β e) = algebraMap R R' (w e)) → Γ.IsHT i M N χ w → Γ'.IsHT (F ≫ i) M' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w' := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M R' _ _ _ Γ' F hF hi' L' _ _ M' β hβ hspan χ w w' hw hHT
  obtain ⟨s, hs, hv⟩ := hHT
  have hs' : Γ'.HasValues (F.appTop.hom s)
      (fun t => (((Units.map (algebraMap R R' : R →* R')).comp χ t : R'ˣ) : R')) := by
    obtain ⟨B, instB, ib, j, j', σ, hj, hji, hj'i, -, hσj, hσj'⟩ := hF.pts
    intro t
    have hb : valAt (σ t) ⊤ le_top s = ib (χ t) := by
      apply hj
      rw [← PositivityTheory.HtPt.Htat.HTBaseChange.valAt_spec_map, hσj, hs t, ← RingHom.comp_apply, hji]
    show valAt (Γ'.pt t).left ⊤ le_top (F.appTop.hom s) = _
    rw [← PositivityTheory.HtPt.Htat.HTBaseChange.valAt_comp_top, ← hσj', PositivityTheory.HtPt.Htat.HTBaseChange.valAt_spec_map, hb, ← RingHom.comp_apply, hj'i]
    simp
  obtain ⟨l', hl'⟩ := PositivityTheory.HtPt.Htat.ht_linear R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) hi'
    L' M' ((Units.map (algebraMap R R' : R →* R')).comp χ) (F.appTop.hom s) hs'
  have key : ∀ e, l' (β e) = Ideal.Quotient.mk (Ideal.span {(N : R')}) (w' (β e)) := by
    intro e
    obtain ⟨v, hv1, hv2, hv3⟩ := hv e
    have hc : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (PositivityTheory.HtPt.Htat.HTBaseChange.qmap (R := R) (R' := R') N))) ≫ v) ≫ Γ.G.hom =
        Spec.map (CommRingCat.ofHom ((algebraMap (R' ⧸ Ideal.span {(N : R')})
          (DualNumber (R' ⧸ Ideal.span {(N : R')}))).comp (Ideal.Quotient.mk _))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
      rw [Category.assoc, hv1, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      all_goals simp [GlobalTheory.CompanionTheory.Ar.dualMap, PositivityTheory.HtPt.Htat.HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    set v'' := hF.cart.lift _ _ hc with hv''
    have h1 := hF.cart.lift_fst _ _ hc
    have h2 := hF.cart.lift_snd _ _ hc
    rw [← hv''] at h1 h2
    have h3 : v'' ≫ F ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R')})))) ≫
        (M'.pt (β e)).left := by
      rw [← Category.assoc, h1, Category.assoc, hv2, hβ e, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      ext a
      all_goals simp [GlobalTheory.CompanionTheory.Ar.dualMap, PositivityTheory.HtPt.Htat.HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    have h4 := hl' (β e) v'' ⟨h2, h3⟩
    rw [← PositivityTheory.HtPt.Htat.HTBaseChange.valAt_comp_top, h1, PositivityTheory.HtPt.Htat.HTBaseChange.valAt_spec_map, hv3] at h4
    have h5 := congrArg TrivSqZeroExt.snd h4
    simp only [GlobalTheory.CompanionTheory.Ar.dualMap, PositivityTheory.HtPt.Htat.HTBaseChange.qmap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, zero_add, add_zero, Ideal.quotientMap_mk] at h5
    rw [← h5, hw]
  have heq : l' = (Ideal.Quotient.mkₐ R' (Ideal.span {(N : R')})).toLinearMap.comp w' :=
    LinearMap.ext_on_range hspan (fun e => by simpa using key e)
  refine ⟨F.appTop.hom s, hs', fun e' => ?_⟩
  obtain ⟨v', ⟨hv'1, hv'2⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N
    (F ≫ i) hi' L' M' e'
  refine ⟨v', hv'1, hv'2, ?_⟩
  rw [hl' e' v' ⟨hv'1, hv'2⟩, heq]
  simp
end

