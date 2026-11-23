module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.ThetaSupremumBounds.StatementE

@[expose] public section

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BlockShape
section
open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker.Shape

open Formalism.BasicNotions Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Col

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

def dPart (s : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : DVar ι a b →₀ ℕ :=
  s.comapDomain Sum.inr Sum.inr_injective.injOn

private theorem jetLin_monomial' (J : (DVar ι a b →₀ ℕ) → K)
    (s : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (r : K) :
    jetLin J (MvPolynomial.monomial s r) =
      r • MvPolynomial.monomial (s.comapDomain Sum.inl Sum.inl_injective.injOn) (J (dPart s)) := by
  have h1 : MvPolynomial.monomial s r = r • MvPolynomial.monomial s (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h1, LinearMap.map_smul]
  congr 1
  unfold jetLin
  rw [show (MvPolynomial.monomial s (1 : K)) = MvPolynomial.basisMonomials _ K s by
    simp [MvPolynomial.coe_basisMonomials], Module.Basis.constr_basis]
  all_goals rfl

theorem map_jetLin {L : Type} [Field L] (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    MvPolynomial.map σ (jetLin J Q) = jetLin (fun m => σ (J m)) (MvPolynomial.map σ Q) := by
  refine MvPolynomial.induction_on' Q (fun s r => ?_) (fun p q hp hq => ?_)
  · rw [MvPolynomial.map_monomial, jetLin_monomial', jetLin_monomial', MvPolynomial.smul_monomial,
      MvPolynomial.smul_monomial, MvPolynomial.map_monomial, smul_eq_mul, smul_eq_mul, map_mul]
  · rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

theorem map_frDet {L : Type} [Field L] (σ : K →+* L) (τ : ι) :
    MvPolynomial.map σ (frDet K a τ) = frDet L a τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp [RingHom.mapMatrix_apply, MvPolynomial.map_X]

theorem map_subD {L : Type} [Field L] (σ : K →+* L) (P : Pol K ι a) :
    MvPolynomial.map σ (subD K ι a b P) = subD L ι a b (MvPolynomial.map σ P) := by
  have h : (MvPolynomial.map σ).comp (subD K ι a b).toRingHom =
      (subD L ι a b).toRingHom.comp (MvPolynomial.map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [subD]
    · intro v
      show MvPolynomial.map σ (subD K ι a b (MvPolynomial.X v)) = subD L ι a b (MvPolynomial.map σ (MvPolynomial.X v))
      rw [MvPolynomial.map_X]
      simp only [subD, MvPolynomial.aeval_X]
      split_ifs <;> simp
  exact RingHom.congr_fun h P

theorem map_jetMap {L : Type} [Field L] (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    MvPolynomial.map σ (jetMap J n P) =
      jetLin (fun m => σ (J m)) (subD L ι a b (MvPolynomial.map σ P * ∏ τ, frDet L a τ ^ n τ)) := by
  simp only [jetMap, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply]
  rw [map_jetLin, map_subD, map_mul, map_prod]
  simp only [map_pow, map_frDet]

end Alg

section Scale

variable {ι : Type} [Fintype ι] {a b : ℕ}

end Scale

section Lift

end Lift

section Base

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
  (c : ℕ) (x : HomE X.E a b)

end Base

end Formalism.L2.Ker.Shape
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivGen
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def conjE {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) : HomE E m n ≃ₗ[𝓞 E] HomE E m n where
  toFun x := g'.toLinearMap ∘ₗ x ∘ₗ g.symm.toLinearMap
  invFun y := g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap
  map_add' x y := LinearMap.ext fun v => by simp
  map_smul' r x := LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, RingHom.id_apply]
    exact equiv_osmul g' r _
  left_inv x := LinearMap.ext fun v => by simp
  right_inv y := LinearMap.ext fun v => by simp

theorem conjE_apply {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) (x : HomE E m n) :
    conjE g g' x = g'.toLinearMap ∘ₗ x ∘ₗ g.symm.toLinearMap := rfl

theorem conjE_symm_apply {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) (y : HomE E m n) :
    (conjE g g').symm y = g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap := rfl

theorem homAt_gmap {m n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n)
    (N : Submodule (𝓞 E) (Sp E m)) (N' : Submodule (𝓞 E) (Sp E n)) :
    homAt S (gmap g N) (gmap g' N') = (homAt S N N').map (conjE g g' : HomE E m n →ₗ[𝓞 E] HomE E m n) := by
  ext x
  rw [Submodule.mem_map_equiv]
  change (∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal (gmap g N), x y ∈ localization₂ P.asIdeal (gmap g' N')) ↔
    ∀ P ∈ S, ∀ u ∈ localization₂ P.asIdeal N, ((conjE g g').symm x) u ∈ localization₂ P.asIdeal N'
  constructor
  · intro h P hP u hu
    have h1 := h P hP (g u) ((mem_localization_gmap P g N (g u)).2 (by simpa using hu))
    rw [mem_localization_gmap] at h1
    simpa [conjE_symm_apply] using h1
  · intro h P hP y hy
    rw [mem_localization_gmap]
    have h1 := h P hP (g.symm y) ((mem_localization_gmap P g N y).1 hy)
    simpa [conjE_symm_apply] using h1

theorem divLat_map {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (Φ : H ≃ₗ[𝓞 E] H) (c : ℕ) (M : Submodule (𝓞 E) H) :
    divLat c (M.map (Φ : H →ₗ[𝓞 E] H)) = (divLat c M).map (Φ : H →ₗ[𝓞 E] H) := by
  ext x
  rw [Submodule.mem_map_equiv]
  simp only [divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mem_map_equiv, map_smul]

theorem mulLat_map {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (Φ : H ≃ₗ[𝓞 E] H) (c : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat c (M.map (Φ : H →ₗ[𝓞 E] H)) = (mulLat c M).map (Φ : H →ₗ[𝓞 E] H) := by
  unfold mulLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext v
  simp

theorem latSum_map {H M : Type} [AddCommGroup H] [Module (𝓞 E) H] [AddCommMonoid M] (Φ : H ≃ₗ[𝓞 E] H)
    (A B : Submodule (𝓞 E) H) (F : H → M) (hF : ∀ x z, z ∈ B.map (Φ : H →ₗ[𝓞 E] H) → F (x + z) = F x) :
    latSum (A.map (Φ : H →ₗ[𝓞 E] H)) (B.map (Φ : H →ₗ[𝓞 E] H)) F = latSum A B (fun x => F (Φ x)) := by
  unfold latSum
  let eA : ↥A ≃ₗ[𝓞 E] ↥(A.map (Φ : H →ₗ[𝓞 E] H)) := Φ.submoduleMap A
  have hq : (B.comap A.subtype).map (eA : ↥A →ₗ[𝓞 E] ↥(A.map (Φ : H →ₗ[𝓞 E] H))) = (B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype := by
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.mem_map_equiv]
    rfl
  let q := Submodule.Quotient.equiv _ _ eA hq
  rw [← finsum_comp_equiv q.toEquiv]
  apply finsum_congr
  intro w
  set s := Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) w
  set r := Function.surjInv (Submodule.Quotient.mk_surjective ((B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype)) (q.toEquiv w)
  have hs : Submodule.Quotient.mk s = w := Function.surjInv_eq _ w
  have hr : Submodule.Quotient.mk r = q.toEquiv w := Function.surjInv_eq _ _
  have hrs : Submodule.Quotient.mk r = (Submodule.Quotient.mk (eA s) : ↥(A.map (Φ : H →ₗ[𝓞 E] H)) ⧸ (B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype) := by
    rw [hr, ← hs]; rfl
  rw [Submodule.Quotient.eq] at hrs
  have hd : ((r : H) - Φ (s : H)) ∈ B.map (Φ : H →ₗ[𝓞 E] H) := hrs
  have := hF (Φ (s : H)) _ hd
  rw [add_sub_cancel] at this
  exact this

theorem finsum_map_of_injective {ι M N : Type} [AddCommMonoid M] [AddCommMonoid N] (T : M →+ N)
    (hT : Function.Injective T) (f : ι → M) : ∑ᶠ i, T (f i) = T (∑ᶠ i, f i) := by
  by_cases h : (Function.support f).Finite
  · exact (map_finsum T h).symm
  · have hs : Function.support (fun i => T (f i)) = Function.support f := by
      ext i
      simp only [Function.mem_support, ne_eq, map_eq_zero_iff T hT]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support (by rw [hs]; exact h), map_zero]

theorem isSdLat_gmap {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (γ : UF E n) : IsSdLat (gmap γ.1 N) := by
  refine ⟨gmap_lattice γ.1 N hN.1, ?_⟩
  change dual (hStd E n) (gmap γ.1 N) = gmap γ.1 N
  rw [dual_gmap γ.1 γ.2, hN.2]

variable {K : Type} [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

theorem kerOf_move_one {th : ThDist E K a b SB V V'} {Sall : Finset (HeightOneSpectrum (𝓞 E))} {D cA cB : ℕ}
    {rho : UF E a →* Module.End K V} {rho' : UF E b →* Module.End K V'} {sS sT : SB → E → K}
    (hth : ThDist.Ok th Sall D rho rho' sS sT)
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (fr : Frs E a SB) (fr' : Frs E b SB) (γ : UF E a) (γ' : UF E b)
    (Ξ Ξ₁ : HomE E a b → K) (c : K)
    (hinv : ∀ x z, z ∈ mulLat cB (homAt Sall N N') → Ξ (x + z) = Ξ x)
    (hΞ : ∀ x, Ξ₁ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = c * Ξ x) :
    kerOf th Sall cA cB (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) Ξ₁ =
      c • ((rho' γ') ∘ₗ kerOf th Sall cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  have hsd := isSdLat_gmap hN γ
  have hsd' := isSdLat_gmap hN' γ'
  have hH := homAt_gmap Sall γ.1 γ'.1 N N'
  have hΞ' : ∀ y, Ξ₁ y = c * Ξ ((conjE γ.1 γ'.1).symm y) := fun y => by
    have := hΞ ((conjE γ.1 γ'.1).symm y)
    rwa [← conjE_apply, LinearEquiv.apply_symm_apply] at this
  have step : (fun x => Ξ₁ x • th (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) cB x) =
      fun x => (c * Ξ ((conjE γ.1 γ'.1).symm x)) • th (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) cB x := by
    funext x
    rw [hΞ']
  unfold kerOf
  rw [step, hH, divLat_map, mulLat_map, latSum_map]
  · unfold latSum
    simp only [LinearEquiv.symm_apply_apply]
    simp only [conjE_apply]
    simp only [hth.equiv γ γ' N fr N' fr' cB _ hN hN']
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · let T : (V →ₗ[K] V') →+ (V →ₗ[K] V') :=
        { toFun := fun f => c • (rho' γ' ∘ₗ f ∘ₗ rho γ⁻¹)
          map_zero' := by simp
          map_add' := fun f g => by simp [LinearMap.add_comp, LinearMap.comp_add, smul_add] }
      have e1 : ∀ w, rho γ⁻¹ (rho γ w) = w := fun w => by
        show (rho γ⁻¹ * rho γ) w = w
        rw [← map_mul, inv_mul_cancel, map_one]; rfl
      have e2 : ∀ w, rho' γ'⁻¹ (rho' γ' w) = w := fun w => by
        show (rho' γ'⁻¹ * rho' γ') w = w
        rw [← map_mul, inv_mul_cancel, map_one]; rfl
      have hT : Function.Injective T := by
        intro f g h
        have h1 := congrArg (fun u => c⁻¹ • u) h
        simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_smul_smul₀ hc] at h1
        refine LinearMap.ext fun v => ?_
        have h2 := LinearMap.congr_fun h1 (rho γ v)
        simp only [LinearMap.comp_apply, e1] at h2
        have h3 := congrArg (rho' γ'⁻¹) h2
        rwa [e2, e2] at h3
      have hTa : ∀ f, T f = c • (rho' γ' ∘ₗ f ∘ₗ rho γ⁻¹) := fun _ => rfl
      rw [← hTa, ← finsum_map_of_injective T hT]
      apply finsum_congr
      intro z
      rw [hTa]
      simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  · intro x z hz
    have hz' : (conjE γ.1 γ'.1).symm z ∈ mulLat cB (homAt Sall N N') := (Submodule.mem_map_equiv _).1 hz
    rw [map_add (f := _), hinv _ _ hz', hth.cong _ _ _ _ cB (x + z) x hsd hsd' (by rw [hH, mulLat_map, add_sub_cancel_left]; exact hz)]

theorem kerOf_move {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {th : ThDist E K a b SB V V'} {Sall : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {rho : UF E a →* Module.End K V} {rho' : UF E b →* Module.End K V'} {sS sT : SB → E → K}
    (hth : ThDist.Ok th Sall (cA * cB) rho rho' sS sT) (hB : 0 < cB)
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (fr : Frs E a SB) (fr' : Frs E b SB) (γ : UF E a) (γ' : UF E b)
    (κ : ∀ P : SB, ↥(GLint E a P.1)) (κ' : ∀ P : SB, ↥(GLint E b P.1))
    (Ξ Ξ₁ : HomE E a b → K) (c : K)
    (hinv : ∀ x z, z ∈ mulLat cB (homAt Sall N N') → Ξ (x + z) = Ξ x)
    (hΞ : ∀ x, (∏ P : SB, sS P (LinearEquiv.det (κ P).1 : Eˣ) * sT P (LinearEquiv.det (κ' P).1 : Eˣ)) *
        Ξ₁ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = c * Ξ x) :
    kerOf th Sall cA cB (gmap γ.1 N) (fun P => γ.1 * fr P * (κ P).1) (gmap γ'.1 N') (fun P => γ'.1 * fr' P * (κ' P).1) Ξ₁ =
      c • ((rho' γ') ∘ₗ kerOf th Sall cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  have hsd := isSdLat_gmap hN γ
  have hsd' := isSdLat_gmap hN' γ'
  have e : kerOf th Sall cA cB (gmap γ.1 N) (fun P => γ.1 * fr P * (κ P).1) (gmap γ'.1 N') (fun P => γ'.1 * fr' P * (κ' P).1) Ξ₁ =
      kerOf th Sall cA cB (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P)
        (fun y => (∏ P : SB, sS P (LinearEquiv.det (κ P).1 : Eˣ) * sT P (LinearEquiv.det (κ' P).1 : Eˣ)) * Ξ₁ y) := by
    unfold kerOf
    congr 1
    funext x
    rw [hth.det (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) cB x κ κ' hsd hsd', smul_smul,
      mul_comm]
  rw [e]
  exact kerOf_move_one hth hN hN' fr fr' γ γ' Ξ _ c hinv hΞ

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkThind
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Lift

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem thInd_eq_lift (hLa : A.LaHyp a b S) (hN : IsSdLat N) (hN' : IsSdLat N') (c : ℕ) (hc : 0 < c) (x s : HomE X.E a b)
    (hs : A.IsLift S N N' c x s) (hv : 0 < volC A.AA S N N') (z : VCx X.Tau a b) :
    A.thInd S N N' c x z =
      ((repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c)).card : ℂ)⁻¹ *
        (alV A.d A.sc (embH (X.embC A.σ₀) A.δ s) *
          opU (HV A.sc) (-(embH (X.embC A.σ₀) A.δ s))
            (sumU (HV A.sc) (alV A.d A.sc) (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c)) (A.e a b N N')) z) := by
  have hH := heisHyp_of A a b S hLa
  obtain ⟨-, hlev⟩ := hH.2.2.2.2 N N' hN hN'
  obtain ⟨hSc, hr1, hr2, -⟩ := hlev c hc
  rw [liftIndep_of A a b S hH N N' c x s hN hN' hc hs z]
  unfold xiInd
  have h1 := twist_induced_vanish _ _ _ _ _ _ hSc _ _ (repsOf_spec _ _ hr1) (repsOf_spec _ _ hr2) (volC A.AA S N N') (A.e a b N N')
  rw [funext h1, opU_smul]
  have h2 : ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) * ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) = ((volC A.AA S N N' : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hv.le]
  have h3 : ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact (Real.sqrt_pos.2 hv).ne'
  rw [← h2]
  field_simp

theorem perO_bot : perO (⊥ : Submodule (𝓞 X.E) X.E) N N' = ⊥ := by
  unfold perO
  rw [Submodule.span_eq_bot]
  rintro z ⟨r, hr, x, -, rfl⟩
  rw [Submodule.mem_bot] at hr
  simp [hr]

theorem volS_self (M : Submodule (𝓞 X.E) (HomE X.E a b)) : volS S M M = 1 := by
  unfold volS
  simp [AddSubgroup.relIndex_self]

theorem volC_pos_of_laHyp (hLa : A.LaHyp a b S) (hN : IsSdLat N) (hN' : IsSdLat N') : 0 < volC A.AA S N N' := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have h0 : ∀ f : HomE X.E a b, f = 0 := fun f => LinearMap.ext fun v => by
      have hv : v = 0 := funext fun i => (Fin.cast ha i).elim0
      rw [hv, map_zero, LinearMap.zero_apply]
    have he : perO A.AA (stdLat X.E a) (stdLat X.E b) = perO A.AA N N' := by
      ext f; rw [h0 f]; simp only [Submodule.zero_mem]
    unfold volC; rw [he, volS_self]; exact one_pos
  rcases Nat.eq_zero_or_pos b with hb | hb
  · have h0 : ∀ f : HomE X.E a b, f = 0 := fun f => LinearMap.ext fun v => funext fun i => (Fin.cast hb i).elim0
    have he : perO A.AA (stdLat X.E a) (stdLat X.E b) = perO A.AA N N' := by
      ext f; rw [h0 f]; simp only [Submodule.zero_mem]
    unfold volC; rw [he, volS_self]; exact one_pos
  have hAA : A.AA ≠ ⊥ := by
    intro h
    have hsd := ((hLa.2.2.2.2.2 N N' hN hN').2).1
    obtain ⟨τ⟩ := hLa.2.1
    have hL : LamC (X.embC A.σ₀) A.δ A.AA N N' = ⊥ := by
      unfold LamC laV; rw [h, perO_bot]; simp
    rw [hL] at hsd
    have hv : (show VCx X.Tau a b from fun _ _ _ => (1 : ℂ)) ∈ dualLat (HV A.sc) (⊥ : AddSubgroup (VCx X.Tau a b)) := by
      intro y hy
      rw [AddSubgroup.mem_bot] at hy
      exact ⟨0, by simp [hy, altE]⟩
    unfold IsSelfDual at hsd
    rw [hsd, AddSubgroup.mem_bot] at hv
    have := congrFun (congrFun (congrFun hv τ) ⟨0, hb⟩) ⟨0, ha⟩
    simp at this
  have hspan {n : ℕ} (L : Submodule (𝓞 X.E) (Sp X.E n))
      (hL : IsSdLat L) : Submodule.span X.E (L : Set (Sp X.E n)) = ⊤ := by
    let W := Submodule.span X.E (L : Set (Sp X.E n))
    change W = ⊤
    by_contra h
    let e : Sp X.E n ≃ₗ⋆[X.E] Sp X.E n := starLinearEquiv X.E
    let g : Sp X.E n →ₗ[X.E] Module.Dual X.E W :=
      (LinearMap.domRestrict' W).comp ((hStd X.E n).comp e.toLinearMap)
    have hdim : Module.finrank X.E (Module.Dual X.E W) < Module.finrank X.E (Sp X.E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : X.E) : a • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd X.E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual X.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : X.E →ₗ[𝓞 X.E] L :=
      ((LinearMap.toSpanSingleton X.E _ (e x)).restrictScalars (𝓞 X.E)).codRestrict L hsmul
    let : Module.Finite (𝓞 X.E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 X.E) X.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective X.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField X.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
  exact covolume_positive X.E a b A.AA S N N' hN.1.fg hN'.1.fg (hspan N hN) (hspan N' hN') hLa.2.2.2.2.1 hAA

theorem thInd_eq_lift' (hLa : A.LaHyp a b S) (hN : IsSdLat N) (hN' : IsSdLat N') (c : ℕ) (hc : 0 < c) (x s : HomE X.E a b)
    (hs : A.IsLift S N N' c x s) (z : VCx X.Tau a b) :
    A.thInd S N N' c x z =
      ((repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c)).card : ℂ)⁻¹ *
        (alV A.d A.sc (embH (X.embC A.σ₀) A.δ s) *
          opU (HV A.sc) (-(embH (X.embC A.σ₀) A.δ s))
            (sumU (HV A.sc) (alV A.d A.sc) (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c)) (A.e a b N N')) z) :=
  thInd_eq_lift A S N N' hLa hN hN' c hc x s hs (volC_pos_of_laHyp A S N N' hLa hN hN') z

end Lift

end Formalism.L2.Ker
end
end

