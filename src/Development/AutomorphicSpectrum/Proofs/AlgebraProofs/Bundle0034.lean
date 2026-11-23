module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0029
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Twomega
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ReBase
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfSurj

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupFromTower
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tower_pdiv_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L), ∃ (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate), X.Realises G e τ ∧ G.height = Module.finrank ℤ La ∧ ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a :=
  @PositivityTheory.HtPt.Twpdiv.tower_pdiv

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerDual
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

open Coalgebra WithConv

theorem exists_hom_dual_of_pairingExtends : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧ ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := PositivityTheory.HtPt.Twpol.exists_linear
      (X.A n) (e n) (lev p n) (fun a => (τ a).pt n) (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := PositivityTheory.HtPt.Twpol.exists_bialgHom (fun a => (τ a).pt n) (sep n)
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

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerFree
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tower_omega : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) [Module.Free O L] [Module.Finite O L] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), ∃ j : G.omega ≃ₗ[O] Module.Dual O L, (∀ (χ : G.dual.Tate) n, X.der n (e n (charElem χ n)).1 (j (dlog G χ))) ∧ ∀ (φ : La →+ La) (dφ : L →ₗ[O] L) (f : G ⟶ G), X.Acts φ dφ → (∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) → ∀ w, j (omegaMap G G f w) = j w ∘ₗ dφ :=
  by
    intro p _ C _ _ _ v O _ _ _ _ _ hO La _ _ _ L _ _ X _ _ G e τ hre
    have counit_eq (n : ℕ) (a : G.A n) :
        Bialgebra.counitAlgHom O (G.A n) a = (e n a).1 1 := by
      have h := hre.pt 0 n a
      rw [map_zero] at h
      exact h
    have mem_sq_iff (n : ℕ) (a : G.A n) :
        a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 ↔
          e n a ∈ BT.augIdeal (X.A n) ^ 2 := by
      have hker : (BT.augIdeal (X.A n)).comap (e n) =
          RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
        ext b
        rw [Ideal.mem_comap, OrderApi.mem_augIdeal, RingHom.mem_ker, counit_eq]
      have hmap : (RingHom.ker (Bialgebra.counitAlgHom O (G.A n))).map (e n) =
          BT.augIdeal (X.A n) := by
        rw [← hker, Ideal.map_comap_of_surjective _ (e n).surjective]
      rw [← hmap, ← Ideal.map_pow]
      constructor
      · exact Ideal.mem_map_of_mem _
      · intro h
        obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ (e n).surjective).1 h
        rwa [← (e n).injective hab]
    have dUnit_eq_zero_iff (n : ℕ) (a : G.A n) :
        PDiv.dUnit (R := O) a = 0 ↔ X.der n (e n a).1 0 := by
      rw [PDiv.dUnit, AugCot.d_eq_zero_iff, mem_sq_iff, map_sub, AlgEquiv.commutes]
      set c := Bialgebra.counitAlgHom O (G.A n) a with hc
      have hc' : X.der n (algebraMap O (X.A n) c).1 0 := X.der_const n c
      constructor
      · intro h
        have hd := PositivityTheory.HtPt.Twomega.der_of_mem_sq X n _ h
        simpa using X.der_add n _ _ _ _ hd hc'
      · intro h
        have hd := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ h hc'
        rw [sub_zero] at hd
        refine X.der_zero n ⟨e n a - algebraMap O (X.A n) c, ?_⟩ hd
        rw [OrderApi.mem_augIdeal, hc, counit_eq]
        exact sub_self _
    have dUnit_eq_iff (n : ℕ) (a b : G.A n) (w : Module.Dual O L)
        (h : X.der n (e n a).1 w) : PDiv.dUnit (R := O) b = PDiv.dUnit (R := O) a ↔ X.der n (e n b).1 w := by
      rw [← sub_eq_zero, PDiv.dUnit, PDiv.dUnit, ← map_sub]
      refine (dUnit_eq_zero_iff n (b - a)).trans ?_
      rw [map_sub]
      constructor
      · intro hd
        simpa using X.der_add n _ _ _ _ hd h
      · intro hd
        have hsub := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ hd h
        rwa [sub_self] at hsub
    have exists_der (n : ℕ) (w : Module.Dual O L) : ∃ a : G.A n, X.der n (e n a).1 w := by
      obtain ⟨f, hf, h⟩ := X.der_onto n w
      exact ⟨(e n).symm ⟨f, hf⟩, by rwa [AlgEquiv.apply_symm_apply]⟩
    let cls (n : ℕ) (w : Module.Dual O L) := PDiv.dUnit (R := O) (exists_der n w).choose
    have dUnit_eq_cls (n : ℕ) (a : G.A n) (w : Module.Dual O L) :
        PDiv.dUnit (R := O) a = cls n w ↔ X.der n (e n a).1 w :=
      dUnit_eq_iff n _ a w (exists_der n w).choose_spec
    have der_res (n : ℕ) (a : G.A (n + 1)) (w : Module.Dual O L)
        (h : X.der (n + 1) (e (n + 1) a).1 w) : X.der n (e n (G.res n a)).1 w :=
      X.der_res n _ _ w h (hre.res n a)
    let toOmega : Module.Dual O L →ₗ[O] G.omega :=
      { toFun := fun w => ⟨fun n => cls n w, fun n => by
          obtain ⟨a, ha⟩ := exists_der (n + 1) w
          change PDiv.cotMap (G.res n) (cls (n + 1) w) = cls n w
          rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.cotMap_d, dUnit_eq_cls]
          exact der_res n a w ha⟩
        map_add' := fun w w' => Subtype.ext (funext fun n => by
          obtain ⟨a, ha⟩ := exists_der n w
          obtain ⟨b, hb⟩ := exists_der n w'
          change cls n (w + w') = cls n w + cls n w'
          rw [← (dUnit_eq_cls _ a w).2 ha, ← (dUnit_eq_cls _ b w').2 hb,
            PDiv.dUnit, PDiv.dUnit, ← map_add (f := _), eq_comm]
          refine (dUnit_eq_cls _ _ _).2 ?_
          rw [map_add (f := _)]
          exact X.der_add n _ _ _ _ ha hb)
        map_smul' := fun r w => Subtype.ext (funext fun n => by
          obtain ⟨a, ha⟩ := exists_der n w
          change cls n (r • w) = r • cls n w
          rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.dUnit, ← map_smul, eq_comm]
          refine (dUnit_eq_cls _ _ _).2 ?_
          rw [map_smul]
          exact PositivityTheory.HtPt.Twomega.der_smul X n r _ _ ha) }
    have toOmega_val (w : Module.Dual O L) (n : ℕ) : (toOmega w).1 n = cls n w := rfl
    have toOmega_bijective : Function.Bijective toOmega := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro w hw
        refine PositivityTheory.HtPt.Twomega.eq_zero_of_cong hO w fun n => ?_
        have h0 : PDiv.dUnit (R := O) (0 : G.A n) = 0 := map_zero _
        have h1 : cls n w = 0 := congrArg (fun x : G.omega => x.1 n) hw
        exact (X.der_unique n _ 0 w ((dUnit_eq_zero_iff n 0).1 h0)).1
          ((dUnit_eq_cls n 0 w).1 (h0.trans h1.symm))
      · intro ω
        choose a ha using fun n => AugCot.d_surjective _ (ω.1 n)
        choose w hw using fun n => X.der_ex n (e n (a n)).1 (e n (a n)).2
        obtain ⟨W, hW⟩ := PositivityTheory.HtPt.Twomega.exists_lim hO w fun n => by
          refine (X.der_unique n _ _ _ (hw n)).1 ?_
          refine (dUnit_eq_iff n _ _ _ (der_res n _ _ (hw (n + 1)))).1 ?_
          rw [← PDiv.cotMap_d, PDiv.dUnit, PDiv.dUnit, ha, ha]
          exact (ω.2 n).symm
        refine ⟨W, Subtype.ext (funext fun n => ?_)⟩
        rw [toOmega_val, ← ha, eq_comm]
        exact (dUnit_eq_cls n _ W).2 ((X.der_unique n _ _ _ (hw n)).2 (hW n))
    let k := LinearEquiv.ofBijective toOmega toOmega_bijective
    have hk (ω : G.omega) (n : ℕ) : ω.1 n = cls n (k.symm ω) :=
      congrArg (fun x : G.omega => x.1 n) (k.apply_symm_apply ω).symm
    refine ⟨k.symm, fun χ n => ?_, fun φ dφ f hφ hf ω => ?_⟩
    · exact (dUnit_eq_cls n _ _).1 (hk (dlog G χ) n)
    · rw [LinearEquiv.symm_apply_eq]
      refine Subtype.ext (funext fun n => ?_)
      obtain ⟨a, ha⟩ := exists_der n (k.symm ω)
      rw [omegaMap_val, hk ω n, ← (dUnit_eq_cls n a _).2 ha, PDiv.cotMap_d]
      exact (dUnit_eq_cls n _ _).2 ((hφ n _ _ (hf n a)).2 _ ha)

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualHopfOrderGaussSum
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

open PositivityTheory.HtPt.Ri in
theorem rank_one_dual_gauss : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ ψ : AddChar F C, ψ ≠ 1 → ∀ AD : HopfOrder (C := C) R F, AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a : F => ψ (h * a)) → FStable (F := F) AD.carrier ∧ ∀ χ : MulChar F R, χ ≠ 1 → ∀ c cD : R, xIdeal AA.carrier χ = Ideal.span {c} → xIdeal AD.carrier χ = Ideal.span {cD} → v (algebraMap R C c) * v (algebraMap R C cD) = v (∑ a, algebraMap R C (χ⁻¹ a) * ψ a) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hM ψ hψ AD hAD
  refine ⟨?_, ?_⟩
  · intro b g hg
    rw [hAD] at hg ⊢
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
    refine Submodule.mem_map.mpr ⟨fun y => ∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a, ?_, ?_⟩
    · intro f' hf'
      obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = ∑ a, u a * f' (b • a) := hu _ (hM b f' hf')
      refine ⟨r, ?_⟩
      show _ = ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * f' y
      rw [hr, push_sum]
      rfl
    · funext h
      show ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * ψ (h * y) = ∑ a, u a * ψ ((b • h) * a)
      rw [push_sum b u (fun y => ψ (h * y))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_eq_mul]
      ring_nf
  · intro χ hχ c cD hc hcD
    set G : C := ∑ a, algebraMap R C (χ⁻¹ a) * ψ a with hG
    have hW : ∀ h : F, ∑ a, algebraMap R C (χ⁻¹ a) * ψ (a * h) = algebraMap R C (χ h) * G := by
      intro h
      have e := wsum_eq χ (fun a => ψ a) (wsum_zero_of_ne hv hχ _) h
      simpa [wsum, G] using e
    have hFt : ∀ t : C, fourier (R := R) (fun h a : F => ψ (h * a)) (fun a => t * algebraMap R C (χ⁻¹ a)) = fun h => t * G * algebraMap R C (χ h) := by
      intro t
      funext h
      show ∑ a, t * algebraMap R C (χ⁻¹ a) * ψ (h * a) = _
      calc ∑ a, t * algebraMap R C (χ⁻¹ a) * ψ (h * a) = t * ∑ a, algebraMap R C (χ⁻¹ a) * ψ (a * h) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [mul_comm h a]
            ring
        _ = _ := by rw [hW h]; ring
    have hq : v ((Fintype.card F : C) - 1) = 1 := v_card_sub_one p hv hpv
    have hcm : (fun a => algebraMap R C c * algebraMap R C (χ a)) ∈ AA.carrier :=
      (mem_xIdeal _ _ _).mp (by rw [hc]; exact Ideal.mem_span_singleton_self c)
    have hDm : (fun a => algebraMap R C cD * algebraMap R C (χ a)) ∈ AD.carrier :=
      (mem_xIdeal _ _ _).mp (by rw [hcD]; exact Ideal.mem_span_singleton_self cD)
    have key : ∀ t : C, (∃ s : R, algebraMap R C s = t * algebraMap R C c) →
        v t * v G ≤ v (algebraMap R C cD) := by
      intro t ⟨s, hs⟩
      have hu : (fun a => t * algebraMap R C (χ⁻¹ a)) ∈ dualLat AA.carrier := by
        intro g hg
        have hsum : wsum χ g = ∑ a : F, χ⁻¹ a • fun x => g (a • x) := by
          funext x
          simp [wsum, Finset.sum_apply, Algebra.smul_def]
        have hm : wsum χ g ∈ AA.carrier := by
          rw [hsum]
          exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hM a g hg)
        obtain ⟨r, hr1⟩ := AA.le_int hm 1
        have hr : r ∈ xIdeal AA.carrier χ := by
          apply (mem_xIdeal _ _ _).2
          convert hm using 1
          funext a
          rw [wsum_eq χ g (wsum_zero_of_ne hv hχ g) a, hr1, mul_comm]
        rw [hc] at hr
        obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        refine ⟨k * s, ?_⟩
        have e : ∑ a, t * algebraMap R C (χ⁻¹ a) * g a = t * wsum χ g 1 := by
          simp only [wsum, mul_one, Finset.mul_sum, mul_assoc]
        show _ = ∑ a, t * algebraMap R C (χ⁻¹ a) * g a
        rw [e, ← hr1, map_mul, map_mul, hs]
        ring
      have hm : (fun h => t * G * algebraMap R C (χ h)) ∈ AD.carrier := by
        rw [hAD, ← hFt]
        exact Submodule.mem_map_of_mem hu
      obtain ⟨s', hs'⟩ : ∃ s' : R, algebraMap R C s' = t * G * algebraMap R C (χ 1) := AD.le_int hm 1
      rw [map_one, map_one, mul_one] at hs'
      have hx : s' ∈ xIdeal AD.carrier χ := by
        rw [mem_xIdeal, hs']
        exact hm
      rw [hcD] at hx
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [← map_mul, ← hs', map_mul, map_mul]
      calc v (algebraMap R C k) * v (algebraMap R C cD) ≤ 1 * v (algebraMap R C cD) := by
            gcongr
            exact hv.map_le_one k
        _ = _ := one_mul _
    rw [hAD] at hDm
    obtain ⟨u, hu, hFu⟩ := Submodule.mem_map.mp hDm
    obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = ∑ a, u a * (algebraMap R C c * algebraMap R C (χ a)) := hu _ hcm
    have hinv : ∑ h, algebraMap R C (χ⁻¹ h) * fourier (R := R) (fun h a : F => ψ (h * a)) u h =
        G * ∑ a, u a * algebraMap R C (χ a) := by
      have e1 : ∀ h, fourier (R := R) (fun h a : F => ψ (h * a)) u h = ∑ a, u a * ψ (h * a) := fun h => rfl
      simp_rw [e1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      calc ∑ h, algebraMap R C (χ⁻¹ h) * (u a * ψ (h * a)) = u a * ∑ h, algebraMap R C (χ⁻¹ h) * ψ (h * a) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun h _ => ?_
            ring
        _ = _ := by rw [hW a]; ring
    have hL : ∑ h, algebraMap R C (χ⁻¹ h) * fourier (R := R) (fun h a : F => ψ (h * a)) u h =
        algebraMap R C cD * ((Fintype.card F : C) - 1) := by
      rw [hFu, ← sum_inv_mul (C := C) χ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    have e2 : ∑ a, u a * (algebraMap R C c * algebraMap R C (χ a)) = algebraMap R C c * ∑ a, u a * algebraMap R C (χ a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e2] at hr
    have hmain : G * algebraMap R C r = algebraMap R C c * algebraMap R C cD * ((Fintype.card F : C) - 1) := by
      linear_combination G * hr - algebraMap R C c * hinv + algebraMap R C c * hL
    have hup : v (algebraMap R C c) * v (algebraMap R C cD) ≤ v G := by
      have h2 := congrArg v hmain
      rw [map_mul, map_mul, map_mul, hq, mul_one] at h2
      rw [← h2]
      calc v G * v (algebraMap R C r) ≤ v G * 1 := by
            gcongr
            exact hv.map_le_one r
        _ = v G := mul_one _
    refine le_antisymm hup ?_
    by_cases hc0 : algebraMap R C c = 0
    · have hG0 : G = 0 := by
        by_contra hG0
        have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
        have h3 := key ((p : C) * G)⁻¹ ⟨0, by rw [hc0, mul_zero, map_zero]⟩
        have e3 : ((p : C) * G)⁻¹ * G = (p : C)⁻¹ := by field_simp
        rw [← map_mul, e3, map_inv₀] at h3
        have h4 := h3.trans (hv.map_le_one cD)
        have hvp : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).mpr hp0
        rw [inv_le_one₀ (pos_iff_ne_zero.mpr hvp)] at h4
        exact absurd hpv (not_lt.mpr h4)
      rw [hG0, hc0]
      simp
    · have h3 := key (algebraMap R C c)⁻¹ ⟨1, by rw [map_one, inv_mul_cancel₀ hc0]⟩
      rw [map_inv₀] at h3
      have hvc : 0 < v (algebraMap R C c) := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hc0)
      rwa [inv_mul_le_iff₀ hvc] at h3

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualModuleConjugateEigenAction
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank

theorem comp_eigProj_eq {E : Type} [Field E] [NumberField E] {C : Type} [Field C]
    [Fintype (E →+* C)] {W : Type} [AddCommGroup W] [Module C W]
    {ρ : 𝓞 E →+* Module.End C W} {s' : E →+* C}
    (hsum : ∀ y, ∑ t, HT.eigProj ρ t y = y) {φ : Module.Dual C W}
    (hφ : ∀ a : 𝓞 E, φ ∘ₗ ρ a = s' (a : E) • φ) :
    φ ∘ₗ HT.eigProj ρ s' = φ := by
  classical
  ext y
  have key : ∀ t, t ≠ s' → φ (HT.eigProj ρ t y) = 0 := by
    intro t ht
    have hmem := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ t y)
    have hex : ∃ a : 𝓞 E, t (a : E) ≠ s' (a : E) := by
      by_contra hc
      push_neg at hc
      exact ht (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
    obtain ⟨a, ha⟩ := hex
    have h1 := LinearMap.congr_fun (hφ a) (HT.eigProj ρ t y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hmem a, map_smul, smul_eq_mul] at h1
    have h2 : (t (a : E) - s' (a : E)) * φ (HT.eigProj ρ t y) = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
  have e : φ y = φ (HT.eigProj ρ s' y) := by
    conv_lhs => rw [← hsum y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single s' (fun t _ ht => key t ht) (by simp)]
  exact e.symm

theorem finrank_eigSp_inf_ker_fst :
    ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  intro E _ _ C _ _ bar s s' W _ _ _ ρ ρH hsum hs hbar hH
  set U := HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) with hU
  set T := HT.eigSp ρ s' with hT
  let F : U →ₗ[C] Module.Dual C T :=
    T.dualRestrict ∘ₗ LinearMap.snd C W (Module.Dual C W) ∘ₗ U.subtype
  have hFapply : ∀ (u : U) (x : T), F u x = (u : W × Module.Dual C W).2 x := fun _ _ => rfl
  have hfst : ∀ u : U, (u : W × Module.Dual C W).1 = 0 := fun u => u.2.2
  have hact : ∀ u : U, ∀ a : 𝓞 E,
      (u : W × Module.Dual C W).2 ∘ₗ ρ a = s' (a : E) • (u : W × Module.Dual C W).2 := by
    intro u a
    have h1 := HT.LatBasic.mem_eigSp.1 u.2.1 (bar a)
    have h2 : (u : W × Module.Dual C W) = (0, (u : W × Module.Dual C W).2) :=
      Prod.ext (hfst u) rfl
    rw [h2, hH, hbar] at h1
    have h3 := congrArg Prod.snd h1
    simpa [hs a] using h3
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 := comp_eigProj_eq hsum (hact u)
    apply Subtype.ext
    refine Prod.ext (hfst u) ?_
    rw [← h0]
    ext y
    have := hFapply u ⟨HT.eigProj ρ s' y, HT.LatBasic.eigProj_mem ρ s' y⟩
    rw [hu] at this
    simpa using this.symm
  have hsurj : Function.Surjective F := by
    intro ψ
    let e : W →ₗ[C] T := LinearMap.codRestrict T (HT.eigProj ρ s') (HT.LatBasic.eigProj_mem ρ s')
    have he : ∀ (b : 𝓞 E) (x : W), e (ρ b x) = s' (b : E) • e x := fun b x =>
      Subtype.ext (HodgeDeterminantLattice.eigProj_act s' b x)
    have hmem : ((0 : W), ψ ∘ₗ e) ∈ U := by
      refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, rfl⟩
      rw [hH]
      refine Prod.ext (by simp) ?_
      ext x
      simp [he, hs, hbar]
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    rw [hFapply]
    have : e x = x := Subtype.ext (HT.LatBasic.eigProj_of_mem x.2)
    simp [this]
  rw [(LinearEquiv.ofBijective F ⟨hinj, hsurj⟩).finrank_eq, Subspace.dual_finrank_eq]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDualPairing
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem chart_comp_zero_mod : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y :=
  @PositivityTheory.HtPt.Gd.chart_comp_zero

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestriction
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem ret_hopf_factor : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → (∃ A' : HopfOrder (C := C) R N', A'.carrier = AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) ∧ (∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι : N' → N)), (fun x => h (π x)) ∈ AA.carrier) ∧ ∀ K' : AddSubgroup N', GenAF p AA.carrier (K'.map ι) → GenAF p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) K' :=
  @PositivityTheory.HtPt.Re.ret_hopf

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrdersOfZmodPExtremes
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_orders_of_zmod_p_extremes : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → (∃ AA : HopfOrder (C := C) R (ZMod p), AA.carrier = intFun R (ZMod p) ∧ FStable (ZMod p) AA.carrier ∧ IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K) ∧ (∃ AA : HopfOrder (C := C) R (ZMod p), AA.carrier = Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x) ∧ AA.carrier ≠ intFun R (ZMod p) ∧ FStable (ZMod p) AA.carrier ∧ IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K) := by
  first | exact @PositivityTheory.HtPt.Ri.inh_af | exact PositivityTheory.HtPt.Ri.inh_af
end

