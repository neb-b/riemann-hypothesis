module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.EqOfTwist
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.PsIrr

open GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem eq_of_twist {χ ψ η : kˣ →* ℂˣ}
    (φ : (detRep (Fin 1) χ).Equiv (twist (detRep (Fin 1) ψ) (detChar (Fin 1) η))) : χ = ψ * η := by
  refine MonoidHom.ext fun x => Units.ext ?_
  let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar _ x
  have hg : Matrix.GeneralLinearGroup.det g = x := by
    ext; simp [g, Matrix.GeneralLinearGroup.scalar]
  obtain ⟨y, hy⟩ := φ.surjective 1
  have h1 := LinearMap.congr_fun (φ.isIntertwining' g) y
  have hy' : φ.toLinearMap y = 1 := hy
  have h2 : detRep (Fin 1) χ g y = (χ x : ℂ) • y := by simp [detRep, hg]
  simp only [LinearMap.comp_apply, h2, map_smul, hy'] at h1
  simpa [twist, detRep, ofChar, hg, mul_comm] using h1

private theorem irr_zero (ψ : Fin 0 → kˣ →* ℂˣ) : (prinSeries ψ).IsIrreducible := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp (points (Fin 0)) ((ofChar (torusChar ψ)).comp (leviTorus k (Fin 0)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun _ => c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
  have E : (detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prinSeries ψ) :=
    Representation.Equiv.mk' ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ (fun F => F.1.1 1)
      (fun c => rfl) (fun F => Subtype.ext (Subtype.ext (funext fun g => by rw [hg g])))
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E (isIrreducible_ofChar _)

set_option synthInstance.maxHeartbeats 400000 in
private theorem irr_prin (H : GlobalTheory.Published.TotallyDisjointProductIrreducible) (n : ℕ) :
    ∀ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) →
      (∀ i j, i ≠ j → ψ i ≠ ψ j ∧ ψ i ≠ ψ j * absPow k 1) → (prinSeries ψ).IsIrreducible := by
  induction n with
  | zero => exact fun ψ _ _ => irr_zero ψ
  | succ n ih =>
    intro ψ hψ hne
    let ψ₁ : Fin n → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd 1 i)
    let ψ₂ : Fin 1 → kˣ →* ℂˣ := fun _ => ψ (Fin.natAdd n 0)
    have happ : Fin.append ψ₁ ψ₂ = ψ := by
      have : ψ₂ = fun i => ψ (Fin.natAdd n i) := funext fun i => by rw [Subsingleton.elim i 0]
      rw [this]
      exact Fin.append_castAdd_natAdd
    have h₁ : (prinSeries ψ₁).IsIrreducible :=
      ih ψ₁ (fun i => hψ _) fun i j hij => hne _ _ fun h => hij (Fin.castAdd_injective _ _ h)
    have h₂ : (prinSeries ψ₂).IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (GlobalTheory.PrinSat.oneEquiv _ (hψ _)) (isIrreducible_ofChar _)
    let σ₁ : Irr k n := ⟨_, prinSeries ψ₁, isSmooth_parInd _ _, h₁⟩
    let σ₂ : Irr k 1 := ⟨_, prinSeries ψ₂, isSmooth_parInd _ _, h₂⟩
    have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
      refine H k n 1 n 1 σ₁ σ₂ _ _ _ _
        (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₁ (ψ := ψ₁) (fun i => hψ _) (.refl _))
        (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₂ (ψ := ψ₂) (fun i => hψ _) (.refl _)) ?_
      rintro a b h j hj ⟨φ⟩
      have e : ψ (Fin.castAdd 1 a) = ψ (Fin.natAdd n 0) * absPow k (j : ℂ) := eq_of_twist φ
      have hab : Fin.castAdd 1 a ≠ Fin.natAdd n 0 := fun h => by
        have := congrArg Fin.val h
        have := a.2
        simp at *
        omega
      obtain rfl | rfl | rfl : j = -1 ∨ j = 0 ∨ j = 1 := by
        have := abs_le.1 hj
        omega
      · refine (hne _ _ hab.symm).2 ?_
        rw [e, mul_assoc, ← absPow_add]
        simp
      · exact (hne _ _ hab).1 (by simpa using e)
      · exact (hne _ _ hab).2 (by simpa using e)
    obtain ⟨E1⟩ := PrinProd.stage_one (k := k) ψ₁ ψ₂
    obtain ⟨E2⟩ := PrinProd.stage_two (k := k) ψ₁ ψ₂
    rw [← happ]
    exact GlobalTheory.Parabolic.isIrreducible_of_equiv (E1.trans E2) hirr

end UpperTheory.V.Hi.PsIrr

theorem UpperTheory.V.Hi.psIrr :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ω : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow k 1) → (PS ω).IsIrreducible ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), π.IsIrreducible → IsSubquotient π (PS ω) → Nonempty (π.Equiv (PS ω)) := by
  intro H k _ _ _ _ n ω hω hne
  have hi : (PS ω).IsIrreducible := by
    refine PsIrr.irr_prin H.loc.disj n _
      (fun i => (hω i).mul (isSmoothChar_of_isUnram (isUnram_absPow k _))) fun i j hij => ⟨fun h => ?_, fun h => ?_⟩
    · exact (hne i j hij).1 (mul_right_cancel h)
    · rw [mul_right_comm] at h
      exact (hne i j hij).2 (mul_right_cancel h)
  exact ⟨hi, fun V _ _ π hπ hs => (hs.nonempty_equiv hπ hi).map fun e => e.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndVec
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi

theorem UpperTheory.V.Hi.indVec :
    ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
        (H K : Subgroup G) (σ : Representation ℂ H W), IsOpen (K : Set G) → ∀ w : W, (∀ h : H, (h : G) ∈ K → σ h w = w) →
        ∃ f : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ), f.1.1 1 = w ∧ f ∈ fixd (GlobalTheory.PRep.smInd H σ) K :=
  _root_.UpperTheory.Reformulated.B.Gr28.indVec
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IsSubquotientOfHasSupport
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this

private theorem multiset_eq_of_sum {Γ : Type} [Monoid Γ] (s t : Multiset (Γ →* ℂ))
    (h : ∀ g, (s.map fun f => f g).sum = (t.map fun f => f g).sum) : s = t :=
  _root_.UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum s t h

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem exists_char {z : WD h} (hz : IsIrrWD z) {n : ℕ} (η : Fin n → Weil h →* ℂˣ)
    (hd : ∀ g, z.charPol g ∣ ∏ j, (X - C (η j g : ℂ))) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), z = WD.lpOfChar h ξ hξ := by
  obtain ⟨m, b, rfl, hirr⟩ := hz
  have hc : ∀ g k, b.ρ g * b.ρ k = b.ρ k * b.ρ g := fun g k => by
    have h1 : b.ρ ((k * g)⁻¹ * (g * k)) = 1 := by
      have h2 := hd ((k * g)⁻¹ * (g * k))
      have h3 : ∀ j, η j ((k * g)⁻¹ * (g * k)) = 1 := fun j => by
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (η j g), inv_mul_cancel]
      simp only [h3, Units.val_one, Finset.prod_const, WD.charPol_mk] at h2
      exact eq_one_of_charpoly_dvd _ (b.semisimple _) h2
    rw [← map_mul, ← map_mul, ← mul_inv_cancel_left (k * g) (g * k), map_mul, h1, mul_one]
  have hsub : ∀ S : Submodule ℂ (Fin m → ℂ), (∀ g v, v ∈ S → b.ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := fun S hS => by
    rcases hirr.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
  haveI : Nontrivial (Fin m → ℂ) := nontrivial_of_irreducible hirr
  have hsc : ∀ g, ∃ c : ℂ, ∀ v, b.ρ g v = c • v := fun g => by
    obtain ⟨c, hcv⟩ := Module.End.exists_eigenvalue (b.ρ g)
    refine ⟨c, fun v => ?_⟩
    rcases hsub (Module.End.eigenspace (b.ρ g) c) (fun k u hu => by
      rw [Module.End.mem_eigenspace_iff] at hu ⊢
      have := LinearMap.congr_fun (hc g k) u
      simp only [Module.End.mul_apply] at this
      rw [this, hu, map_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.mp hcv)
    · exact Module.End.mem_eigenspace_iff.mp (h ▸ Submodule.mem_top)
  have hm : m = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
    rcases hsub (Submodule.span ℂ {v}) (fun g u hu => by
      obtain ⟨c, h⟩ := hsc g
      rw [h]; exact Submodule.smul_mem _ _ hu) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hv
    · have := finrank_span_singleton (K := ℂ) hv
      rw [h, finrank_top] at this
      simpa using this
  subst hm
  have hsc : ∀ f : Module.End ℂ (Fin 1 → ℂ), ∀ v, f v = f 1 0 • v := fun f v => by
    have hv : v = v 0 • (1 : Fin 1 → ℂ) := by
      funext i; rw [Subsingleton.elim i 0]; simp
    funext i
    rw [Subsingleton.elim i 0]
    conv_lhs => rw [hv, map_smul]
    simp [mul_comm]
  let c : Weil h →* ℂ :=
    { toFun := fun σ => b.ρ σ 1 0
      map_one' := by simp
      map_mul' := fun σ τ => by
        rw [map_mul, Module.End.mul_apply, hsc (b.ρ σ) (b.ρ τ 1)]; simp }
  have hker : ∀ σ, b.ρ σ = 1 → c.toHomUnits σ = 1 := fun σ hσ => by
    ext
    show b.ρ σ 1 0 = 1
    simp [hσ]
  have hN : b.N = 0 := by
    obtain ⟨n, hn⟩ := b.nilpotent
    have e : b.N = b.N 1 0 • (1 : Module.End ℂ (Fin 1 → ℂ)) := LinearMap.ext fun v => by
      rw [hsc b.N v]; rfl
    rw [e, _root_.smul_pow, one_pow] at hn
    have := congrFun (LinearMap.congr_fun hn 1) 0
    have h2 : b.N 1 0 ^ n = 0 := by simpa using this
    rw [e, pow_eq_zero_iff'.mp h2 |>.1, zero_smul]
  refine ⟨c.toHomUnits, b.smooth.of_le hker, ?_⟩
  refine WD.sound ⟨LinearEquiv.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · funext i
    rw [WDRep.ofChars_ρ, diagEnd_apply, LinearEquiv.refl_apply, LinearEquiv.refl_apply, hsc (b.ρ σ) v]
    rfl
  · simp [hN]

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

private theorem charPol_ofChar (H : Laws a ha ε rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

private theorem hasSupport_iff (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : Laws a ha ε rc)
    (x : IrrGL (k := w.adicCompletion E)) {n : ℕ} (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) :
    HasSupport x.rep (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) ↔
      ∀ g, (rc x).charPol g = ∏ j, (X - C (ω j (a g) : ℂ)) := by
  refine ⟨fun hs g => ?_, fun hp => ?_⟩
  · rw [H.supp x _ hs g, Multiset.map_map, Finset.prod_eq_multiset_prod]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => charPol_ofChar H _ _ g)
  obtain ⟨s, hs⟩ := SupportRing.exists_hasSupport hZ x
  have hch : ∀ y ∈ s, ∃ χ hχ, IrrGL.ofChar χ hχ = y := fun y hy => by
    obtain ⟨ξ, hξ, e⟩ := exists_char ((H.cusp y).1 (hs.isCusp hy)) (fun j => (ω j).comp a) fun g => by
      refine Dvd.dvd.trans ?_ (hp g).dvd
      rw [H.supp _ s hs g]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol g) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    exact ⟨χ, hχ, (H.bij.1 (e.trans (H.one χ hχ).symm)).symm⟩
  let S := {χ : (w.adicCompletion E)ˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL (k := w.adicCompletion E) := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL (k := w.adicCompletion E)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := hch y hy
      exact ⟨⟨χ, hχ⟩, e⟩
  let c : S → (w.adicCompletion E)ˣ →* ℂ := fun χ => (Units.coeHom ℂ).comp χ.1
  have hc : Function.Injective c := fun χ ψ e =>
    Subtype.ext (MonoidHom.ext fun y => Units.ext (DFunLike.congr_fun e y))
  let t' : Multiset S := Finset.univ.val.map fun i => ⟨ω i, hω i⟩
  have htt : t = t' := by
    refine Multiset.map_injective hc (multiset_eq_of_sum _ _ fun y => ?_)
    obtain ⟨g, rfl⟩ := ha.surj y
    have h1 : (((t.map c).map fun f => f (a g)).map fun r => X - C r).prod =
        (((t'.map c).map fun f => f (a g)).map fun r => X - C r).prod := by
      have h2 := (H.supp x _ hs g).symm.trans (hp g)
      simp only [Multiset.map_map, Function.comp_def, t'] at h2 ⊢
      rw [Finset.prod_eq_multiset_prod] at h2
      refine Eq.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun χ _ => ?_)) h2
      exact (charPol_ofChar H χ.1 χ.2 g).symm
    have h3 := congrArg Polynomial.roots h1
    rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h3
    rw [h3]
  rw [htt, Multiset.map_map] at hs
  exact hs

end

private theorem isSubquotient_of_hasSupport (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (τ : IrrRep (GL (Fin n) k)) (μ : Fin n → kˣ →* ℂˣ)
    (hμ : ∀ i, IsSmoothChar (μ i)) (hs : HasSupport τ.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (μ i) (hμ i))) :
    IsSubquotient τ.ρ (prinSeries μ) := by
  have hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n := by simp [IrrGL.ofChar]
  refine IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have h1 := SupportRing.pos_pc_sub hΨ hs τ.smooth τ.irr
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ _ hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp τ.smooth τ.irr ?_
  have h2 := h1 (IrrGL.of τ.ρ τ.smooth τ.irr)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL (k := k)), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)

theorem UpperTheory.V.Hi.psRec :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ rc, IsRec h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (IsSubquotient σ.ρ (PS ω) ↔ ∀ s, (rc (algNorm σ)).charPol s = ∏ j, (X - C (ω j (a s) : ℂ))) := by
  intro P L Ω _ _ _ _ _ n w A h a ha rc hrc σ ω hω
  obtain ⟨a', ha', ε, -, H⟩ := hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := P.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective P.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion L) (((n : ℂ) - 1) / 2)) :=
    fun i => (hω i).mul (isSmoothChar_absPow _)
  have e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  have e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i) := fun i =>
    IrrGL.tw_ofChar _ _ _ _
  rw [← hasSupport_iff P.loc.zel H (algNorm σ) ω hω]
  let τ : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, σ.ρ, σ.smooth, σ.irred⟩
  constructor
  · intro hs
    have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hμ τ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
    have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
    simp only [Multiset.map_map, Function.comp_def, ← e1, IrrGL.nu_nu, e0, IrrGL.nu_zero] at h2
    exact h2
  · intro hs
    have h2 := SupportRing.hasSupport_nu hs (((n : ℂ) - 1) / 2)
    have e2 : (algNorm σ).nu (((n : ℂ) - 1) / 2) = IrrGL.of σ.ρ σ.smooth σ.irred := by
      rw [algNorm, IrrGL.nu_nu, add_comm, e0, IrrGL.nu_zero]
    have key : ∀ (x y : IrrGL (k := w.adicCompletion L)) s, x = y → HasSupport x.rep s → HasSupport y.rep s := by
      rintro _ _ _ rfl h; exact h
    have h3 := (key _ _ _ e2 h2).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
    simp only [Multiset.map_map, Function.comp_def, e1] at h3
    exact isSubquotient_of_hasSupport P.loc.zel τ _ hμ h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SatTUnif
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem satT_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (a : G) (hf : (MulAction.orbit K (a : G ⧸ K)).Finite) (S : Set G)
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ K, ∃ y ∈ K, g = x * a * y) (v : V) :
    dc ρ K K a v = GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) v := by
  classical
  haveI := hf.to_subtype
  have h1 : dc ρ K K a v = ∑ᶠ q : MulAction.orbit K (a : G ⧸ K), ρ (q : G ⧸ K).out v :=
    (LinearMap.applyₗ (R := ℂ) (M₂ := V) v).toAddMonoidHom.map_finsum (Set.toFinite _)
  rw [h1, finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out v), finsum_mem_def, GlobalTheory.LFun.heckeVec]
  refine finsum_congr fun c => ?_
  have h2 : c ∈ MulAction.orbit K (a : G ⧸ K) ↔ c.out ∈ S := by
    rw [hS]
    constructor
    · rintro ⟨x, hx⟩
      have hx' : ((x.1 * a : G) : G ⧸ K) = (c.out : G ⧸ K) := hx.trans c.out_eq'.symm
      exact ⟨x, x.2, _, QuotientGroup.eq.1 hx', by group⟩
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      change ((x * a : G) : G ⧸ K) = c
      rw [← c.out_eq', e]
      exact (QuotientGroup.mk_mul_of_mem _ hy).symm
  by_cases hc : c.out ∈ S
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (h2.2 hc)]; simp
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (mt h2.1 hc)]; simp

private theorem satT_unif (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    Formalism.UG.IsUnifV L w (unif (w.adicCompletion L) : w.adicCompletion L) := by
  haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (valuation (w.adicCompletion L))
    (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hu : valuation (w.adicCompletion L) (unif (w.adicCompletion L) : w.adicCompletion L) =
      uniformizer (w.adicCompletion L) := by
    refine Classical.epsilon_spec (p := fun x : (w.adicCompletion L)ˣ =>
      valuation (w.adicCompletion L) (x : w.adicCompletion L) = uniformizer (w.adicCompletion L)) ?_
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer (w.adicCompletion L))
    refine ⟨Units.mk0 x ?_, hx⟩
    rintro rfl
    exact (zero_lt_iff.2 (by simp) : 0 < uniformizer (w.adicCompletion L)).ne ((map_zero _).symm.trans hx)
  obtain ⟨p, hp⟩ := GlobalTheory.LFun.exists_isUnifV w
  unfold Formalism.UG.IsUnifV at hp ⊢
  have h1 : Valued.v (unif (w.adicCompletion L) : w.adicCompletion L) < (1 : WithZero (Multiplicative ℤ)) :=
    he.lt_one_iff_lt_one.1 (hu.trans_lt uniformizer_lt_one)
  have h2 : valuation (w.adicCompletion L) p < 1 := he.lt_one_iff_lt_one.2 (by rw [hp]; decide)
  have h3 := (he _ _).1 ((le_uniformizer_iff.2 h2).trans_eq hu.symm)
  rw [hp] at h3
  refine le_antisymm ?_ h3
  change _ ≤ WithZero.exp (-1 : ℤ)
  rw [← WithZero.lt_mul_exp_iff_le (by simp), ← WithZero.exp_add]
  simpa using h1

private theorem satT_num (q n j : ℕ) (hq : q ≠ 0) :
    ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j =
      (q : ℂ) ^ (j * (j - 1) / 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have h2 : ((j * (j - 1) / 2 : ℕ) : ℂ) = (j : ℂ) * ((j : ℂ) - 1) / 2 := by
    rw [← Nat.choose_two_right, Nat.cast_choose_two]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q), ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, h2]
  push_cast
  rw [← Complex.cpow_add _ _ hq']
  congr 1
  ring

private theorem satT_pol (q n : ℕ) (hq : q ≠ 0) (B : Multiset ℂˣ) (hB : B.card = n) (a : ℕ → ℂ)
    (ha : ∀ j ≤ n, a j = GlobalTheory.LFun.satEig q n B j) :
    ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a := by
  have hc : (UpperTheory.V.Af.algSat n q B).card = n := by simp [UpperTheory.V.Af.algSat, hB]
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, UpperTheory.V.Hi.heckePol]
  refine Finset.sum_congr rfl fun j hj => ?_
  have e : (UpperTheory.V.Af.algSat n q B).esymm j =
      ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
    rw [← smul_eq_mul, Multiset.pow_smul_esymm, UpperTheory.V.Af.algSat]
    congr 2
    simp
  rw [ha j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), e, satT_num q n j hq, GlobalTheory.LFun.satEig]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem UpperTheory.V.Hi.satT :
    ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → GlobalTheory.LFun.KGL w (n := n) = KO (w.adicCompletion L) (Fin n) ∧ ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j, ∀ v ∈ fixd σ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp σ.ρ j v = a j • v) ∧ ((UpperTheory.V.Af.algSat n (normV w) B).map fun b => X - C b).prod = heckePol n (normV w) a := by
  intro L _ _ n w σ B hB
  have hK : KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  have hq : Formalism.UG.qV L w = normV w := by
    simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨hK.symm, fun j => GlobalTheory.LFun.satEig (normV w) n B (min j n), by simp [GlobalTheory.LFun.satEig, Multiset.esymm], ?_,
    satT_pol (normV w) n (hq ▸ GlobalTheory.LFun.qV_ne_zero w) B hB.card
      (fun j => GlobalTheory.LFun.satEig (normV w) n B (min j n)) (fun j hj => by rw [min_eq_left hj])⟩
  intro j v hv
  by_cases h0 : v = 0
  · simp [h0]
  rw [hK] at hv
  have h1 := (hB.2 v (GlobalTheory.LGrp.mem_fixed.2 hv) h0).2.2.2 _ (satT_unif L w) (min j n) (min_le_right _ _)
  rw [hq] at h1
  refine Eq.trans ?_ h1
  rw [sphOp, hK]
  refine satT_dc σ.ρ _ _ (Formalism.UG.P.orbit_coset_finite _ (Formalism.UG.Final.GLintComm L w n) _) _ (fun g => ?_) v
  have hal : (al (w.adicCompletion L) n j).val =
      Formalism.UG.diagJ n (unif (w.adicCompletion L) : w.adicCompletion L) (min j n) := by
    rw [UpperTheory.V.Hi.al, upow, val_diagT, Formalism.UG.diagJ]
    congr 1
    funext i
    have := i.2
    by_cases h : (i : ℕ) < j
    · simp [h]
    · simp [h]
  simp only [Set.mem_setOf_eq, ← hal, ← Units.val_mul, Units.val_inj]
end

