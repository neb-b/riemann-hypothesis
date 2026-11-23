module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.deRhamRational_of_conj :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (p : GL (Fin n) (Qbar l)), Continuous r → (∀ g, r' g = p * r g * p⁻¹) → ∀ (HT : (F →+* Qbar l) → Multiset ℤ) (Q : ↥(Weil h) → ℂ[X]), DRat ι h r HT Q → DRat ι h r' HT Q := by
  intro hD F Ω _ _ _ _ _ l _ ι A w h n r r' p hc e HT Q H O _ _ _ Bw hj
  obtain ⟨h1, h2, h3⟩ := H O Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨c1, -, -, c4⟩ := GlobalTheory.ConjLocal.local_conj l (UpperTheory.V.Loc.PP l) F Ω O _ Bw n _ _ p e
  have hp := hD.isPstAt T Bw r (Units.continuous_val.comp hc) h1
  have hw := (GlobalTheory.PstConj.main F Ω l ι n _ _ ⟨T⟩ w A h O Bw hj r r' p e hp).2
  exact ⟨c1 h1, fun τ L τ' hτ => c4 _ _ (h2 τ L τ' hτ), fun s => by rw [hw]; exact h3 s⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfExtensionByCharacter
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem charpoly_of_exact {K M₀ M M₂ : Type} [Field K] [AddCommGroup M₀] [Module K M₀] [FiniteDimensional K M₀]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] [AddCommGroup M₂] [Module K M₂] [FiniteDimensional K M₂]
    (f : M₀ →ₗ[K] M) (p : M →ₗ[K] M₂) (hf : Function.Injective f) (hp : Function.Surjective p)
    (he : Function.Exact f p) (T₀ : End K M₀) (T : End K M) (T₂ : End K M₂) (h₀ : ∀ x, f (T₀ x) = T (f x))
    (h₂ : ∀ x, p (T x) = T₂ (p x)) : T.charpoly = T₀.charpoly * T₂.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker p, T x ∈ LinearMap.ker p := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [h₂, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker p) T hA]
  congr 1
  · let e : M₀ ≃ₗ[K] ↥(LinearMap.ker p) :=
      (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.1 he).symm)
    have he' : T.restrict hA = e.conj T₀ := by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact Subtype.ext (h₀ x).symm
    rw [he', LinearEquiv.charpoly_conj]
  · let e := p.quotKerEquivOfSurjective hp
    have he' : (LinearMap.ker p).mapQ (LinearMap.ker p) T (fun x hx => hA x hx) = e.symm.conj T₂ := by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
      apply e.injective
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
      simp only [e, LinearMap.quotKerEquivOfSurjective_apply_mk, h₂]
      rfl
    rw [he', LinearEquiv.charpoly_conj]

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e := IsModel.unique B r (hm₁.enlarge h₁) (hm₂.enlarge h₂)
  have a₁ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι B h hj h₁ r₁ hV₁
  have a₂ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι B h hj h₂ r₂ hV₂
  rw [e] at a₁
  exact e₁.trans (a₁.symm.trans a₂)

section Blocks

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)

private theorem exists_model {m : ℕ} (r : ↥Gw →* GL (Fin m) (Om l)) (L : FinExt l) (hL : B.LL.1 ≤ L.1)
    (hr : ∀ g i j, (r g : Matrix (Fin m) (Fin m) (Om l)) i j ∈ L.1) : ∃ r₂, IsModel B r L r₂ := by
  let M : ↥Gw →* Matrix (Fin m) (Fin m) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hr g i j⟩
      map_one' := by
        ext i j
        simp [Matrix.one_apply, apply_ite]
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  exact ⟨M.toHomUnits, hL, by ext g i j; rfl⟩

private theorem blocks {n : ℕ} (r : ↥Gw →* GL (Fin (n + 1)) (Om l)) (r' : ↥Gw →* GL (Fin n) (Om l))
    (ψ : ↥Gw →* (Om l)ˣ)
    (h0 : ∀ g (i : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i.succ 0 = 0)
    (h1 : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) 0 0 = (ψ g : Om l))
    (h2 : ∀ g (i j : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i.succ j.succ =
      (r' g : Matrix (Fin n) (Fin n) (Om l)) i j)
    (L : FinExt l) (r₁ : ↥Gw →* GL (Fin (n + 1)) ↥L.1) (hm : IsModel B r L r₁) :
    ∃ (r₀ : ↥Gw →* GL (Fin 1) ↥L.1) (r₂ : ↥Gw →* GL (Fin n) ↥L.1)
      (f : (Fin 1 → ↥L.1) →ₗ[↥L.1] (Fin (n + 1) → ↥L.1)) (p : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1)),
      IsModel B (GlobalTheory.TripleGal.rk1 ψ) L r₀ ∧ IsModel B r' L r₂ ∧
      (∀ g v, f (B.repE L r₀ g v) = B.repE L r₁ g (f v)) ∧ (∀ g v, p (B.repE L r₁ g v) = B.repE L r₂ g (p v)) ∧
      Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p := by
  have e₁ : ∀ g i j, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i j =
      (((r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i j : ↥L.1) : Om l) := fun g i j => by rw [← hm.2]; rfl
  have eψ : ∀ g i j, (GlobalTheory.TripleGal.rk1 ψ g : Matrix (Fin 1) (Fin 1) (Om l)) i j = ψ g := fun g i j => by
    rw [Subsingleton.elim j i]
    exact Matrix.diagonal_apply_eq (fun _ : Fin 1 => (ψ g : Om l)) i
  obtain ⟨r₀, m₀⟩ := exists_model B (GlobalTheory.TripleGal.rk1 ψ) L hm.1 fun g i j => by
    rw [eψ, ← h1, e₁]; exact SetLike.coe_mem _
  obtain ⟨r₂, m₂⟩ := exists_model B r' L hm.1 fun g i j => by
    rw [← h2, e₁]; exact SetLike.coe_mem _
  have k0 : ∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i.succ 0 = 0 :=
    fun g i => Subtype.ext ((e₁ g _ _).symm.trans (h0 g i))
  have k1 : ∀ g, (r₀ g : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) 0 0 :=
    fun g => Subtype.ext (by rw [← e₁, h1, ← eψ g 0 0, ← m₀.2]; rfl)
  have k2 : ∀ g i j, (r₂ g : Matrix (Fin n) (Fin n) ↥L.1) i j =
      (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i.succ j.succ :=
    fun g i j => Subtype.ext (by rw [← e₁, h2, ← m₂.2]; rfl)
  have ap : ∀ {m : ℕ} (s : ↥Gw →* GL (Fin m) ↥L.1) g v i,
      B.repE L s g v i = ∑ j, (s (B.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) i j * v j := fun s g v i => rfl
  refine ⟨r₀, r₂, LinearMap.single ↥L.1 (fun _ => ↥L.1) 0 ∘ₗ LinearMap.proj 0, LinearMap.funLeft ↥L.1 ↥L.1 Fin.succ,
    m₀, m₂, fun g v => funext fun i => ?_, fun g v => funext fun i => ?_, fun x y hxy => funext fun i => ?_,
    LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n), fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rw [ap]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [ap, k1, Fin.sum_univ_succ]
    · simp [k0, Fin.sum_univ_succ]
  · rw [ap, LinearMap.funLeft_apply, ap, Fin.sum_univ_succ, k0]
    simp [k2]
  · rw [Subsingleton.elim i 0]
    simpa using congrFun hxy 0
  · refine ⟨fun _ => x 0, funext fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simpa using (congrFun hx i).symm
  · rintro ⟨y, rfl⟩
    funext i
    simp

end Blocks

set_option maxHeartbeats 1000000 in
theorem UpperTheory.deRham_rational_of_extension_by_character :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin (n + 1)) (Qbar l)) (r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous r → (∀ g (i : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) i.succ 0 = 0) → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) 0 0 = (ψ g : Qbar l)) → (∀ g (i j : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) (Qbar l)) i j) → ∀ (c : (F →+* Qbar l) → ℤ) (HT : (F →+* Qbar l) → Multiset ℤ) (β : ↥(Weil h) → ℂ) (Q : ↥(Weil h) → ℂ[X]), DRat ι h r (fun τ => c τ ::ₘ HT τ) (fun s => (X - C (β s)) * Q s) → DRat ι h (GlobalTheory.TripleGal.rk1 ψ) (fun τ => {c τ}) (fun s => X - C (β s)) → DRat ι h r' HT Q := by
  intro hB F Ω _ _ _ _ _ l _ ι A w h n r r' ψ hc h0 h1 h2 c HT β Q hr hψ O _ _ _ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨d₁, j₁, p₁⟩ := hr O Bw hj
  obtain ⟨-, j₀, p₀⟩ := hψ O Bw hj
  have dr : ∀ {m : ℕ} (L : FinExt l) (s : ↥(Dec (F := F) A) →* GL (Fin m) ↥L.1),
      IsDR ((UpperTheory.V.Loc.PP l).PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE (UpperTheory.V.Loc.PP l) L s := fun L s => by
    rw [IsDR, finrank_fin_fun]; rfl
  refine ⟨?_, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · obtain ⟨L, r₁, hm, hd⟩ := d₁
    obtain ⟨r₀, r₂, f, p, -, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    exact ⟨L, r₂, m₂, (dr L r₂).1 (GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T Bw.Kw L _ _ _ _ _ _ f p hf hp
      fi ps (LinearMap.exact_iff.1 ex).symm ((dr L r₁).2 hd)).2.1⟩
  · obtain ⟨L, r₁, hm, hd, τ₁, t₁, hcount⟩ := j₁ τ LL' τ' hτ
    obtain ⟨r₀, r₂, f, p, m₀, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    obtain ⟨-, d₂, hadd⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T Bw.Kw L _ _ _ _ _ _ f p hf hp
      fi ps (LinearMap.exact_iff.1 ex).symm ((dr L r₁).2 hd)
    refine ⟨L, r₂, m₂, (dr L r₂).1 d₂, τ₁, t₁, fun a => ?_⟩
    have a₀ := IsJumpsAt.count_eq (UpperTheory.V.Loc.PP l) m₀ t₁ (j₀ τ LL' τ' hτ) a
    have a₁ := hcount a
    have a₂ : Bw.multE (UpperTheory.V.Loc.PP l) L r₁ τ₁ a = Bw.multE (UpperTheory.V.Loc.PP l) L r₀ τ₁ a + Bw.multE (UpperTheory.V.Loc.PP l) L r₂ τ₁ a :=
      (hadd τ₁ a).2.1
    beta_reduce at a₀ a₁
    rw [← Multiset.singleton_add, Multiset.count_add, Nat.cast_add, a₀, a₂] at a₁
    exact add_left_cancel a₁
  · obtain ⟨L, r₁, hm, hV⟩ := hB.isPstAt T Bw r (Units.continuous_val.comp hc) d₁
    obtain ⟨r₀, r₂, f, p, m₀, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    obtain ⟨V₀, V₂, wi, ws, wex⟩ := UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L _ _ _ _ _ _ f p hf hp fi ps ex hV
    haveI := hV.finite
    haveI := V₀.finite
    haveI := V₂.finite
    have a₀ := p₀ s
    have a₁ := p₁ s
    beta_reduce at a₀ a₁
    rw [wdAt_of_model _ ι Bw h hj _ L r₀ m₀ V₀, DpstMap.charPol_wdPst _ ι Bw h hj _ V₀] at a₀
    rw [wdAt_of_model _ ι Bw h hj _ L r₁ hm hV, DpstMap.charPol_wdPst _ ι Bw h hj _ hV,
      charpoly_of_exact _ _ wi ws wex _ _ _ (DpstMap.wdLin_wdRho _ ι Bw h hj hf s)
        (DpstMap.wdLin_wdRho _ ι Bw h hj hp s), a₀] at a₁
    rw [wdAt_of_model _ ι Bw h hj _ L r₂ m₂ V₂, DpstMap.charPol_wdPst _ ι Bw h hj _ V₂]
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) a₁
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsDpstFrobeniusEigenvectorOfCharacter
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
set_option synthInstance.maxHeartbeats 400000


open Module in
private theorem exists_int_basis {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V), ∀ g i j, ‖e.repr (ρ g (e j)) i‖ ≤ 1 := by
  classical
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₀ := Module.finBasis ℚ_[l] V
  let Λ : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (e₀ p.2))
  have hc : Continuous fun g : G => (fun i j => e₀.repr (ρ g (e₀ j)) i) :=
    continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap (e₀.coord i)).comp (hρ _)
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨c, hc0, hcC⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    exact ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩
  have hle : Λ ≤ Submodule.span ℤ_[l] (Set.range fun i => c • e₀ i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, rfl⟩
    change ρ g (e₀ j) ∈ _
    rw [← e₀.sum_repr (ρ g (e₀ j))]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : ‖e₀.repr (ρ g (e₀ j)) i / c‖ ≤ 1 := by
      rw [norm_div]
      refine div_le_one_of_le₀ (le_trans ?_ hcC) (norm_nonneg _)
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm (fun i j => e₀.repr (ρ g (e₀ j)) i) i)).trans
        (hC _ ⟨g, rfl⟩)
    let z : ℤ_[l] := ⟨_, h1⟩
    have h2 : e₀.repr (ρ g (e₀ j)) i • e₀ i = z • c • e₀ i := by
      change _ = (e₀.repr (ρ g (e₀ j)) i / c) • c • e₀ i
      rw [smul_smul, div_mul_cancel₀ _ hc0]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Submodule.IsLattice ℚ_[l] Λ :=
    Submodule.IsLattice.of_fg ℚ_[l] ((Submodule.fg_span (Set.finite_range _)).of_le hle)
  haveI : Submodule.IsFullLattice ℚ_[l] Λ :=
    { span_eq_top := by
        rw [eq_top_iff, ← e₀.span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨(1, i), by simp⟩ }
  haveI : Module.Free ℤ_[l] Λ := Submodule.IsLattice.free ℚ_[l] Λ
  haveI : Module.Finite ℤ_[l] Λ := Submodule.IsLattice.finite ℚ_[l] Λ
  let b := Module.finBasis ℤ_[l] Λ
  have hst : ∀ g, ∀ x ∈ Λ, ρ g x ∈ Λ := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, j⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * h, j), by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Λ.add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Λ.smul_mem a hx
  refine ⟨_, b.extendOfIsFullLattice ℚ_[l], fun g i j => ?_⟩
  have h1 : ρ g (b.extendOfIsFullLattice ℚ_[l] j) =
      ∑ k, (algebraMap ℤ_[l] ℚ_[l] (b.repr ⟨_, hst g _ (b j).2⟩ k)) • b.extendOfIsFullLattice ℚ_[l] k := by
    have := congrArg Λ.subtype (b.sum_repr ⟨_, hst g _ (b j).2⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [Basis.extendOfIsFullLattice_apply]
    exact this.symm
  rw [h1, Basis.repr_sum_self]
  exact PadicInt.norm_le_one _

private theorem map_iterFrob {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (k : ℕ)
    (x : WittVector p R) :
    WittVector.map (iterateFrobenius R p (k + 1)) x =
      WittVector.frobenius (WittVector.map (iterateFrobenius R p k) x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext i
  simp [iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]


open TensorProduct GlobalTheory.Pst in
private theorem phiV_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (k : ℕ) (v : V) (w : Ainf l) :
    (phiV P LL V ^ k) (v ⊗ₜ[ℚ_[l]] (Polynomial.C (AI.ιA w) : Bst P)) =
      v ⊗ₜ[ℚ_[l]] (Polynomial.C (AI.ιA (WittVector.map (iterateFrobenius _ l k) w)) : Bst P) := by
  induction k with
  | zero =>
    rw [pow_zero, Module.End.one_apply]
    congr 3
    ext i
    simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, phiV_tmul, phiSt_C, map_iterFrob, AI.ιA_φ]

open GlobalTheory.Pst in
private theorem coe_phiD_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {K : FinExt l} (ρ : Representation LL ↥(GK K) V) (k : ℕ) (x : ↥(Dpst P ρ)) :
    ((phiD P ρ ^ k) x).1 = (phiV P LL V ^ k) x.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, coe_phiD, ih]

open TensorProduct GlobalTheory.Pst GlobalTheory.UnramifiedRep GlobalTheory.UnramifiedCrys in
private theorem period {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    {K K' : FinExt l} (hKK : K.1 ≤ K'.1) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V]
    [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] [Nontrivial V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (m : ↥(GK K) → LL) (ρ : Representation LL ↥(GK K) V)
    (hρ : ∀ g v, ρ g v = m g • v) (hc : ∀ x, Continuous fun g => ρ g x)
    (hI : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (g : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup → m g = 1) :
    ∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ (g : ↥(GK K)) (a b : ℕ),
      (∀ c : ↥(MaximalUnramifiedExtension l), (g : GQ l) (((frobUr l ^ b) c : ↥(MaximalUnramifiedExtension l)) : Om l) = (((frobUr l ^ a) c : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      actD P ρ g ((phiD P ρ ^ b) x) = m g • (phiD P ρ ^ a) x := by
  classical
  have := compactSpace_GK K'
  let ρ' : Representation LL ↥(GK K') V := resTo ρ hKK
  let ρq : Representation ℚ_[l] ↥(GK K') V :=
    { toFun := fun g => (ρ' g).restrictScalars ℚ_[l]
      map_one' := by rw [map_one]; rfl
      map_mul' := fun g h => by rw [map_mul]; rfl }
  have hinc : Continuous (Subgroup.inclusion (GK_le hKK)) := continuous_inclusion (GK_le hKK)
  have hcont : ∀ x, Continuous fun g => ρ' g x := fun x => (hc x).comp hinc
  obtain ⟨n, e, hint⟩ := exists_int_basis ρq hcont
  obtain ⟨M, hM⟩ := exists_matrixHom ρ' e hint
  obtain ⟨W, hW, hWg, hWc⟩ := UpperTheory.exists_algebraic_vector_spanning_subspace P AI K' M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h : ∀ x, ρ' g x = x := fun x => by
        refine (hρ _ x).trans ?_
        rw [hI (Subgroup.inclusion (GK_le hKK) g) g.2 ((UpperTheory.V.Loc.memIK K' g).1 hg), one_smul]
      rw [← map_one M]
      ext i j
      rw [hM, hM, h, map_one, Module.End.one_apply])
  haveI : Nontrivial P.R.B := nontrivial_B P
  haveI : Nontrivial (Ainf l) := AI.ιA.domain_nontrivial
  haveI : Nonempty (Fin n) := e.index_nonempty
  obtain ⟨i0, j0, hij⟩ : ∃ i j, W i j ≠ 0 := by
    by_contra hc
    push Not at hc
    have : W = 0 := Matrix.ext hc
    rw [this, Matrix.det_zero] at hW
    exact not_isUnit_zero hW
  let x : V ⊗[ℚ_[l]] Bst P := ∑ i, e i ⊗ₜ (Polynomial.C (AI.ιA (W i j0)) : Bst P)
  have hx : x ∈ Dpst P ρ := ⟨K', hKK, (mem_Dst P _).2 fun g => by
    have h1 : ∀ i, AI.ιA (W i j0) = ∑ k, e.repr (ρ' g (e k)) i • P.actQ g (AI.ιA (W k j0)) := fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← hWg g, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, Matrix.map_apply, Matrix.map_apply, ιA_zlW AI Ti, hM, ← AI.ιA_act, Algebra.smul_def]
      rfl
    have h2 : x = ∑ i, ∑ k, (e.repr (ρ' g (e k)) i • e i) ⊗ₜ[ℚ_[l]]
        (Polynomial.C (P.actQ g (AI.ιA (W k j0))) : Bst P) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1 i, map_sum, tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Polynomial.smul_C, smul_tmul]
    conv_rhs => rw [h2, Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [stRep_tmul, actSt_C, ← sum_tmul, e.sum_repr]⟩
  refine ⟨⟨x, hx⟩, fun h0 => hij ?_, fun g a b hg => Subtype.ext ?_⟩
  · have h1 : x = 0 := congrArg Subtype.val h0
    have h2 := congrArg (fun y => TensorProduct.lid ℚ_[l] _ (LinearMap.rTensor (Bst P) (e.coord i0) y)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, map_sum, LinearMap.rTensor_tmul, lid_tmul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero,
      Polynomial.C_eq_zero] at h2
    exact AI.ιA_inj (h2.trans (map_zero _).symm)
  · rw [coe_actD, Submodule.coe_smul, coe_phiD_pow, coe_phiD_pow]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, map_sum, phiV_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stRep_tmul, actSt_C, hρ, smul_tmul', ← AI.ιA_act]
    congr 3
    ext k
    obtain ⟨r, hr, hy⟩ := hWc i j0 k
    exact UpperTheory.Ainf_action_tilt_fixed_of_frobenius_relation P AI g a b hg _ r hr hy

theorem UpperTheory.exists_dpst_frobenius_eigenvector_of_character :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' L : FinExt l), K.1 ≤ K'.1 → ∀ (m : ↥(GK K) →* (↥L.1)ˣ) (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)), (∀ g v, ρ g v = (m g : ↥L.1) • v) → Continuous (fun g => ((m g : ↥L.1) : Om l)) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (g : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup → m g = 1) → ∃ x : ↥(GlobalTheory.Pst.Dpst P ρ), x ≠ 0 ∧ ∀ (g : ↥(GK K)) (a b : ℕ), (∀ c : ↥(MaximalUnramifiedExtension l), (g : GQ l) (((GlobalTheory.Pst.frobUr l ^ b) c : ↥(MaximalUnramifiedExtension l)) : Om l) = (((GlobalTheory.Pst.frobUr l ^ a) c : ↥(MaximalUnramifiedExtension l)) : Om l)) → GlobalTheory.Pst.actD P ρ g ((GlobalTheory.Pst.phiD P ρ ^ b) x) = (m g : ↥L.1) • (GlobalTheory.Pst.phiD P ρ ^ a) x := by
  intro l _ P AI Ti K K' L hKK m ρ hρ hm hI
  have := L.2
  have : IsModuleTopology ℚ_[l] (Fin 1 → ↥L.1) := isModuleTopologyOfFiniteDimensional
  have h1 : Continuous fun g => (m g : ↥L.1) := continuous_induced_rng.2 hm
  exact period P AI Ti hKK (fun g => (m g : ↥L.1)) ρ hρ
    (fun x => (h1.smul (continuous_const (y := x))).congr fun g => (hρ g x).symm)
    (fun g h h' => by rw [hI g h h', Units.val_one])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HasLocalLanglandsOfIsLocalArtinOfCMDatum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem emb_eq {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {u : Plc M} (h : IsPlaceOver A u) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l M Ω (Dec (F := M) A) O) (hj : GlobalTheory.Pst.Induces Bw)
    (δ : M) (d : ℚ_[l]) (hd : Bw.j (algebraMap M Ω δ) = algebraMap ℚ_[l] (Om l) d) (τ : Emb l u) :
    τ.1 (algebraMap M (u.adicCompletion M) δ) = algebraMap ℚ_[l] (Om l) d := by
  let jE : M →+* Om l := Bw.j.comp (algebraMap M Ω)
  let t : M →+* Om l := τ.1.comp (algebraMap M (u.adicCompletion M))
  have hjE : ∀ x : 𝓞 M, ‖jE (x : M)‖ < 1 ↔ x ∈ u.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (h x)
  have ht : ∀ x : 𝓞 M, ‖t (x : M)‖ < 1 ↔ x ∈ u.asIdeal := fun x => by
    refine ⟨fun hx => ?_, norm_lt_one_of_contEmb u τ.1 τ.2 x⟩
    by_contra hxu
    obtain ⟨y, a, ha, e⟩ := u.isMaximal.exists_inv hxu
    have h1 : ‖t (a : M)‖ < 1 := norm_lt_one_of_contEmb u τ.1 τ.2 a ha
    have h2 : ‖t ((y * x : 𝓞 M) : M)‖ < 1 := by
      rw [show ((y * x : 𝓞 M) : M) = (y : M) * (x : M) from map_mul _ _ _, map_mul, norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (PI.CompDegEF.norm_le_one_of_integer t y) (norm_nonneg _) hx
    have h3 := IsUltrametricDist.norm_add_le_max (t ((y * x : 𝓞 M) : M)) (t (a : M))
    rw [← map_add (f := _), show ((y * x : 𝓞 M) : M) + (a : M) = 1 by
      rw [← map_add (algebraMap (𝓞 M) M), e, map_one], map_one, norm_one] at h3
    exact absurd (h3.trans_lt (max_lt h2 h1)) (lt_irrefl _)
  have hn := GlobalTheory.GalFirstClause.Emb.norm_eq_of_samePlace jE t u (hj.mem_placesOver h) hjE ht
  have key := GlobalTheory.GalFirstClause.Emb.norm_tensLift_le jE t hn ((1 : ℚ_[l]) ⊗ₜ[ℚ] δ - d ⊗ₜ[ℚ] (1 : M))
  simp only [map_sub, GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul, mul_one] at key
  rw [show jE δ = algebraMap ℚ_[l] (Om l) d from hd, sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at key
  exact key

theorem UpperTheory.hasLocalLanglands_of_isLocalArtin_of_CMDatum :
    HeckeLAdicCharacter → HeckeLAdicCharacterDeRham → AlgebraicCharacterWD → DeRhamPotSemistable → ∀ {M Ω : Type} [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {u : Plc M} (h : IsPlaceOver A u) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l M Ω (Dec (F := M) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ) (δ : M) (d : ℚ_[l]), δ ≠ 0 → Bw.j (algebraMap M Ω δ) = algebraMap ℚ_[l] (Om l) d → (∀ φ : M →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ) → ∀ (wt : Emb l u → ℤ) (a : Weil h →* (u.adicCompletion M)ˣ), IsLocalArtin h a → UpperTheory.V.Loc.HasLT h Bw hj ι wt a := by
  intro hH hR hW hD M Ω _ _ _ _ _ _ l _ A u h O _ _ _ Bw hj ι δ d hδ hd hc wt a ha
  classical
  let r : Emb l u → (M →+* ℂ) := fun τ => (ι.toRingHom.comp τ.1).comp (algebraMap M (u.adicCompletion M))
  have hrδ : ∀ τ, r τ δ = ι (algebraMap ℚ_[l] (Om l) d) := fun τ =>
    congrArg ι (emb_eq h Bw hj δ d hd τ)
  have hr : Function.Injective r := fun τ τ' e => by
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap M u).equalizer τ.2 τ'.2 (funext fun k => ?_)
    exact ι.injective (DFunLike.congr_fun e k)
  let g : (M →+* ℂ) → ℤ := Function.extend r wt 0
  let n : (M →+* ℂ) → ℤ := fun φ => g (ComplexEmbedding.conjugate φ) - g φ
  have hn : ∀ τ, n (r τ) = -wt τ := fun τ => by
    have h1 : g (r τ) = wt τ := hr.extend_apply _ _ _
    have h2 : g (ComplexEmbedding.conjugate (r τ)) = 0 := by
      refine Function.extend_apply' _ _ _ ?_
      rintro ⟨τ', e⟩
      have e1 : r τ' δ = starRingEnd ℂ (r τ δ) := DFunLike.congr_fun e δ
      rw [hc, hrδ τ', ← hrδ τ, self_eq_neg] at e1
      exact hδ ((map_eq_zero _).1 e1)
    simp only [n, h1, h2, zero_sub]
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.AlgCharUnr.exists_algChar_unr M l Fact.out n 0 fun φ => by
    have : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
    simp only [n, this]
    ring
  obtain ⟨art, hart, hμ⟩ := hH M Ω
  obtain ⟨μ, ⟨hμc, hL⟩, -⟩ := hμ l ι χ n hχ
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hrk : GlobalTheory.TripleGal.rk1 (μ.comp (Dec (F := M) A).subtype) =
      (GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := M) A).subtype := by
    ext σ i j
    simp [GlobalTheory.TripleGal.rk1]
  have hcμ : Continuous fun σ : ↥(Dec (F := M) A) =>
      (((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := M) A).subtype σ : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμc.comp (continuous_subtype_val (p := fun x => x ∈ Dec (F := M) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hcp := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := u) χ
  refine ⟨μ.comp (Dec (F := M) A).subtype, (χ.loc u).comp a, hμc.comp continuous_subtype_val, ha.smooth hcp.1,
    ?_, fun σ => ?_, fun σ => ?_⟩
  · rw [hrk]
    exact hD.isPstAt T Bw _ hcμ (hR M Ω l _ _ ⟨T⟩ ι art hart χ n μ hχ hμc hL u A h O Bw hj).1
  · have h1 := hL.loc (a σ) _ (ha.glob art hart σ)
    haveI := finite_contEmb (l := l) u
    have h2 : locPow ι n u (a σ) * ∏ᶠ τ : Emb l u, τ.1 (a σ : u.adicCompletion M) ^ wt τ = 1 := by
      unfold locPow
      rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finprod_eq_one_of_forall_eq_one fun τ => ?_
      rw [← zpow_add₀ ((map_ne_zero τ.1).2 (a σ).ne_zero), show n _ = -wt τ from hn τ, neg_add_cancel, zpow_zero]
    show ((χ.loc u (a σ) : ℂˣ) : ℂ) = ι (((μ (σ : G M Ω) : (Qbar l)ˣ) : Qbar l) * _)
    rw [h1, mul_assoc, h2, mul_one, ι.apply_symm_apply]
  · rw [hrk, hW M Ω l _ _ ⟨T⟩ ι art hart χ n μ hχ hμc hL u A h O Bw hj _ hcp a ha, eig_lpOfChar]
    exact Multiset.mem_singleton_self _
end

