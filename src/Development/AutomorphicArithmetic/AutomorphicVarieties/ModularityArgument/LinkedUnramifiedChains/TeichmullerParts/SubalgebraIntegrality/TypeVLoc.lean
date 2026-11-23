module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
open GlobalTheory.PRep GlobalTheory.TypeTwo.PowIrrProof

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.J.D.TypeVAux

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
    (h : ∀ g, (s.map fun f => f g).sum = (t.map fun f => f g).sum) : s = t := by
  classical
  have key : ∀ (u : Multiset (Γ →* ℂ)) (g : Γ),
      Finsupp.linearCombination ℂ (fun f : Γ →* ℂ => (f : Γ → ℂ))
        (u.map fun f => Finsupp.single f (1 : ℂ)).sum g = (u.map fun f => f g).sum := fun u g => by
    induction u using Multiset.induction_on with
    | empty => simp
    | cons a u ih => simp [ih]
  have cnt : ∀ (u : Multiset (Γ →* ℂ)) (f : Γ →* ℂ),
      (u.map fun f => Finsupp.single f (1 : ℂ)).sum f = (u.count f : ℂ) := fun u f => by
    induction u using Multiset.induction_on with
    | empty => simp
    | cons a u ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih, Multiset.count_cons, Finsupp.single_apply]
      by_cases e : a = f
      · simp [e, add_comm]
      · simp [e, Ne.symm e]
  have h1 := linearIndependent_monoidHom Γ ℂ (funext fun g => (key s g).trans ((h g).trans (key t g).symm))
  ext f
  have h2 := (cnt s f).symm.trans ((congrArg (fun u => u f) h1).trans (cnt t f))
  exact_mod_cast h2

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem prinSeries_irreducible {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : ∀ i j, ω j ≠ ω i * absPow k 1) : (prinSeries ω).IsIrreducible := by
  let x : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ω i) (hω i)
  have hx : ∀ i, (x i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (x i).1 = n := by simp [x, IrrGL.ofChar]
  have hnu : ∀ i j, x j ≠ (x i).nu 1 := fun i j e => by
    simp only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
    exact h i j e
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (x i) (hx i)) x hd
      (fun i j => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx i) (hx j) (hnu i j) (hnu j i))
      (fun i => (single_spec (hx i)).2.1)
  let e₀ := Equiv.sigmaUnique (Fin n) fun _ => Fin 1
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ e₀ (stdBlocks (fun i => (x i).1) hd) _).1
    (piTensor fun i => detRep (Fin 1) (ω i))
  have hM : (multiProd e₀ fun i => detRep (Fin 1) (ω i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv
      (p.trans (multiProdEquiv (stdBlocks (fun i => (x i).1) hd)
        fun i => equivRep (IrrRep.det (Fin 1) (ω i) (hω i)))).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI : Nontrivial (IndSp _ _) := by
    obtain ⟨S, f, hf⟩ := GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e₀ ω
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  have equiv_local {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ)
      [Nontrivial W] (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨E⟩ := equiv_local (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hM

end Loc

section WD

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

private theorem charPol_ofChar (H : UpperTheory.V.Z.Win.LawsV a ha ε rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

private theorem hasSupport_of_charPol (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : UpperTheory.V.Z.Win.LawsV a ha ε rc)
    (x : IrrGL (k := w.adicCompletion E)) {n : ℕ} (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) (hp : ∀ g, (rc x).charPol g = ∏ j, (X - C (ω j (a g) : ℂ))) :
    HasSupport x.rep (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) := by
  obtain ⟨s, hs⟩ := SupportRing.exists_hasSupport hZ x
  have hch : ∀ y ∈ s, ∃ χ hχ, IrrGL.ofChar χ hχ = y := fun y hy => by
    obtain ⟨ξ, hξ, e⟩ := exists_char ((H.cusp y).1 (hs.isCusp hy)) (fun j => (ω j).comp a) fun g => by
      refine Dvd.dvd.trans ?_ (hp g).dvd
      rw [H.supp _ s hs g]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol g) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    have e' := e.trans (H.one χ hχ).symm
    have hy1 : y.1 = 1 := by
      rw [← H.dim y, e', H.dim]
      simp [IrrGL.ofChar]
    have hg : UpperTheory.Zero.LLC.Good y :=
      ⟨{y}, hasSupport_self (hs.isCusp hy), fun u hu => Or.inl (by rwa [Multiset.mem_singleton.1 hu])⟩
    exact ⟨χ, hχ, H.inj _ _ hg e'.symm⟩
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

end WD

end UpperTheory.V.Z.J.D.TypeVAux
