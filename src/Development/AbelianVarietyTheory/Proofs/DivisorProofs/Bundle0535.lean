module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Formalism.LocalToGlobal.Divisibility.DefGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitaryS
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.TypesMirror

theorem sameBlock_swap {p q : ℕ} (a b : Ix p q) :
    sameBlock (p := q) (q := p) a.swap b.swap ↔ sameBlock a b := by
  cases a <;> cases b <;> simp [sameBlock]

theorem card_filter_swap {p q : ℕ} (P : Ix p q → Prop) (Q : Ix q p → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ b, P b ↔ Q b.swap) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_equiv (Equiv.sumComm (Fin p) (Fin q)) ?_
  intro b
  simpa using h b

theorem blattner_swap {p q : ℕ} (lam : Ix q p → ℚ) (a : Ix p q) :
    blattner (fun b : Ix p q => lam b.swap) a = blattner lam a.swap := by
  unfold blattner rhoNC
  rw [card_filter_swap (fun b : Ix p q => ¬ sameBlock a b ∧ lam b.swap < lam a.swap)
      (fun b : Ix q p => ¬ sameBlock a.swap b ∧ lam b < lam a.swap)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => ¬ sameBlock a b ∧ lam a.swap < lam b.swap)
      (fun b : Ix q p => ¬ sameBlock a.swap b ∧ lam a.swap < lam b)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => sameBlock a b ∧ lam b.swap < lam a.swap)
      (fun b : Ix q p => sameBlock a.swap b ∧ lam b < lam a.swap)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => sameBlock a b ∧ lam a.swap < lam b.swap)
      (fun b : Ix q p => sameBlock a.swap b ∧ lam a.swap < lam b)
      (fun b => by rw [sameBlock_swap])]

theorem shiftNu_swap {p q : ℕ} (r s : ℕ) (lam : Ix q p → ℚ) (a : Ix p q) :
    shiftNu (cPair r s) (blattner (fun b : Ix p q => lam b.swap)) a =
      shiftNu (cPair s r) (blattner lam) a.swap := by
  cases a <;> simp only [shiftNu, blattner_swap, Sum.swap_inl, Sum.swap_inr, cPair] <;> ring

theorem ofBlocks_swap {p q : ℕ} (l₁ l₂ : List ℚ) :
    (ofBlocks l₁ l₂ : Ix p q → ℚ) = fun b => (ofBlocks l₂ l₁ : Ix q p → ℚ) b.swap := by
  funext b; cases b <;> rfl

theorem isParam_swap {p q : ℕ} (lam : Ix q p → ℚ) (h : IsParam lam) :
    IsParam (fun b : Ix p q => lam b.swap) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.comp (Equiv.sumComm (Fin p) (Fin q)).injective, ?_, fun a => h3 _, fun a b => h4 _ _⟩
  intro a b hab
  apply h2
  cases a <;> cases b <;> simpa [posC] using hab

theorem jointShape_swap {p q r s : ℕ} (lam : Ix q p → ℚ) (lam' : Ix s r → ℚ)
    (h : JointShape q p s r (blattner lam) (blattner lam')) :
    JointShape p q r s (blattner fun b => lam b.swap) (blattner fun b => lam' b.swap) := by
  obtain ⟨a, b, c, d, ha, hc, hb, hd, pa, pb, pc, pd, l1, l2, l3, l4, e1, e2⟩ := h
  refine ⟨c, d, a, b, hc, ha, hd, hb, pc, pd, pa, pb, l2, l1, l4, l3, ?_, ?_⟩
  · funext x
    rw [shiftNu_swap, e1, ofBlocks_swap]
    simp
  · funext x
    rw [shiftNu_swap, e2, ofBlocks_swap]
    simp

theorem hypA_swap {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de) :
    HypA t ga de al be := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hp : (ga ++ de ++ al ++ be).Perm (al ++ be ++ ga ++ de) := by
    rw [List.append_assoc (ga ++ de), List.append_assoc (al ++ be)]
    exact List.perm_append_comm
  refine ⟨h1, by omega, h5, h6, h3, h4, hp.nodup_iff.mpr h7,
    fun e he => h8 e (List.perm_append_comm.mem_iff.mp he),
    fun e he => h9 e (List.perm_append_comm.mem_iff.mp he),
    fun e he => h10 e (hp.mem_iff.mp he), fun e he => h11 e (hp.mem_iff.mp he)⟩

theorem types_mirror : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) ∧ IsParam (lamM' t al be ga de) ∧ (∀ a, (0 < lamA al be ga de a → 0 ≤ shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a) ∧ (lamA al be ga de a < 0 → shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a ≤ 0)) ∧ (∀ c, ((t : ℚ) / 2 < lamM' t al be ga de c → 0 ≤ shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c) ∧ (lamM' t al be ga de c ≤ (t : ℚ) / 2 → shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c ≤ 0)) := by
  intro t al be ga de h
  obtain ⟨k1, -, k3, k4, k5⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t ga de al be (hypA_swap h)
  have e1 : lamA al be ga de = fun b => lamA ga de al be b.swap := ofBlocks_swap _ _
  have e2 : lamM' t al be ga de = fun b => lamA' t ga de al be b.swap := ofBlocks_swap _ _
  rw [e1, e2]
  refine ⟨jointShape_swap _ _ k1, isParam_swap _ k3, fun a => ?_, fun c => ?_⟩
  · rw [shiftNu_swap]; exact k4 a.swap
  · rw [shiftNu_swap]; exact k5 c.swap

end GlobalTheory.TypesMirror
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.M2ModelEstablished
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AbhHeightOne

theorem closureEtaleAt_of_etale_integralClosure_localization : ∀ (A₁ R₁ D₁ : Type) [CommRing A₁] [CommRing R₁] [Algebra A₁ R₁] [CommRing D₁]
    [Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) D₁] (P₁ : Ideal R₁) [P₁.IsPrime],
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ D₁).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] D₁))) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ D₁ P₁ := by
  intro A₁ R₁ D₁ _ _ _ _ _ P₁ _ h
  letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ D₁).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ R₁ D₁
  unfold GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt
  let e : GlobalTheory.KeyOriginNoeth.closure A₁ R₁ D₁ ≃ₐ[R₁] integralClosure R₁ D₁ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hb := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R₁)
    (S := Localization.AtPrime P₁) (B := D₁) P₁.primeCompl
  let Φ : Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginNoeth.closure A₁ R₁ D₁ ≃ₐ[Localization.AtPrime P₁]
      integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] D₁) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (AlgEquiv.ofBijective _ hb)
  exact Algebra.Etale.of_equiv Φ.symm

theorem etale_integralClosure_of_torsor_field : ∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M)) := by
  intro S S₁ K K₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj q hq hqu π hπ y hy M _ _ act htor
  obtain ⟨ι, _, L, _, _, hfd, hgal, hdeg, ⟨e⟩⟩ := GlobalTheory.T.zmodTorsor_field_eq_prod_galois K M q act hq htor
  have hi : ∀ i, Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L i)) := fun i => by
    letI : Algebra S (L i) := ((algebraMap K (L i)).comp (algebraMap S K)).toAlgebra
    haveI : IsScalarTower S K (L i) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI := hfd i
    haveI := hgal i
    obtain ⟨hram, hsep⟩ := GlobalTheory.T.ramificationIdx_dvd_of_galois_degree_dvd_unit_dvr S K (L i) q hq hqu (hdeg i)
    exact GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer S S₁ K K₁ (L i) hinj q hq hqu π hπ y hy hram hsep
  classical
  haveI := GlobalTheory.T.etale_integralClosure_pi_of_etale S₁ ι (fun i => K₁ ⊗[K] L i) hi
  let Ψ : K₁ ⊗[K] M ≃ₐ[K₁] ∀ i, K₁ ⊗[K] L i :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (Algebra.TensorProduct.piRight K K₁ K₁ L)
  exact Algebra.Etale.of_equiv (Ψ.restrictScalars S₁).symm.mapIntegralClosure

theorem closureEtaleAt_of_root_of_uniformiser : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA) P₁ := by
  intro A R _ _ _ _ _ hAR A₁ R₁ _ _ _ _ _ hA₁R₁ f hf φ hφ β hβ DA _ _ q act hq hqu htor P₁ _ hd₁ hd π hπ y hy
  exact closureEtaleAt_of_etale_integralClosure_localization A₁ R₁ _ P₁ (GlobalTheory.T.etale_integralClosure_torsor_of_fraction_fields etale_integralClosure_of_torsor_field A R hAR A₁ R₁ hA₁R₁ f hf φ hφ β hβ DA q act hq hqu htor P₁ hd₁ hd π hπ y hy)

end GlobalTheory.AbhHeightOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMemSpanField
section
namespace GlobalTheory.StandardLatticeSpan

open NumberField

variable {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}

theorem mem_range_iff (a : E) :
    f a ∈ (algebraMap (𝓞 E') E').range ↔ a ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · rintro ⟨c, hc⟩
    have h1 : IsIntegral ℤ (f a) := hc ▸ c.isIntegral_coe
    have h2 : IsIntegral ℤ (f.symm (f a)) :=
      map_isIntegral_int (f.symm : E' →+* E) h1
    rw [f.symm_apply_apply] at h2
    exact ⟨⟨a, h2⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨f (algebraMap _ _ c), map_isIntegral_int (f : E →+* E') c.isIntegral_coe⟩, rfl⟩

theorem mem_span_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E') :
    y ∈ Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (L : Set (Fin n → E)))
      ↔ ∃ x ∈ L, (fun i ↦ f (x i)) = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, L.zero_mem, by ext i; simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, L.add_mem ha hb, by ext i; simp⟩
    | smul c y _ hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨d, hd⟩ := (mem_range_iff f (f.symm (algebraMap (𝓞 E') E' c))).1
        ⟨c, by rw [f.apply_symm_apply]⟩
      refine ⟨d • a, L.smul_mem d ha, ?_⟩
      ext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hd, RingEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem map_mem_span_int (s : Set (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span (𝓞 E) s) :
    (fun i ↦ f (x i)) ∈
      Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' s) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i ↦ f ((0 : Fin n → E) i)) = 0 := by ext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i ↦ f ((y + z) i)) = (fun i ↦ f (y i)) + (fun i ↦ f (z i)) := by ext i; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨d, hd⟩ := (mem_range_iff f (algebraMap (𝓞 E) E c)).2 ⟨c, rfl⟩
    have : (fun i ↦ f ((c • y) i)) = d • (fun i ↦ f (y i)) := by
      ext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hd]
    rw [this]; exact Submodule.smul_mem _ _ hy

theorem map_mem_span_field (s : Set (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E s) :
    (fun i ↦ f (x i)) ∈
      Submodule.span E' ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' s) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i ↦ f ((0 : Fin n → E) i)) = 0 := by ext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i ↦ f ((y + z) i)) = (fun i ↦ f (y i)) + (fun i ↦ f (z i)) := by ext i; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (fun i ↦ f ((c • y) i)) = f c • (fun i ↦ f (y i)) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ hy

theorem stdH_map [StarRing E] [StarRing E'] (hf : ∀ x : E, f (star x) = star (f x))
    (x y : Fin n → E) :
    Formalism.BasicNotions.stdH E' n (fun i ↦ f (x i)) (fun i ↦ f (y i)) = f (Formalism.BasicNotions.stdH E n x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.BasicNotions.stdH, map_sum, map_mul, hf]

theorem isSDLat_map {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}
    [NumberField E] [NumberField E'] [StarRing E] [StarRing E']
    (hf : ∀ x : E, f (star x) = star (f x)) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Formalism.BasicNotions.IsSDLat E n L) :
    Formalism.BasicNotions.IsSDLat E' n (Submodule.span (𝓞 E')
      ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (L : Set (Fin n → E)))) := by
  obtain ⟨⟨s, hs⟩, htop, hdual⟩ := hL
  have surj : ∀ y : Fin n → E', ∃ x : Fin n → E, (fun i ↦ f (x i)) = y :=
    fun y => ⟨fun i => f.symm (y i), by ext i; simp⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.fg_def]
    refine ⟨(fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (s : Set (Fin n → E)),
      s.finite_toSet.image _, le_antisymm ?_ ?_⟩
    · apply Submodule.span_mono
      apply Set.image_mono
      rw [← hs]; exact Submodule.subset_span
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact map_mem_span_int f _ (hs ▸ hx)
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := surj y
    have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := htop ▸ Submodule.mem_top
    exact Submodule.span_mono Submodule.subset_span (map_mem_span_field f _ hx)
  · intro y
    obtain ⟨y, rfl⟩ := surj y
    constructor
    · intro hy x hx
      obtain ⟨y', hy', e⟩ := (mem_span_iff f L _).1 hy
      obtain ⟨x, hx', rfl⟩ := (mem_span_iff f L _).1 hx
      rw [← e, stdH_map f hf, mem_range_iff]
      exact (hdual y').1 hy' x hx'
    · intro h
      refine (mem_span_iff f L _).2 ⟨y, (hdual y).2 fun x hx => ?_, rfl⟩
      rw [← mem_range_iff f, ← stdH_map f hf]
      exact h _ ((mem_span_iff f L _).2 ⟨x, hx, rfl⟩)

end GlobalTheory.StandardLatticeSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitComponentMulMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem overPullback_unit_comp_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    (η[(Over.pullback p).obj G]).left ≫ pullback.fst G.hom p = p ≫ (η[G]).left := by
  have hmap : ((Over.pullback p).map η[G]).left ≫ pullback.fst G.hom p =
      pullback.fst (𝟙_ (Over S)).hom p ≫ (η[G]).left := by
    simp
  have hε : (Functor.LaxMonoidal.ε (Over.pullback p)).left ≫ pullback.fst (𝟙_ (Over S)).hom p = p := by
    have h1 : pullback.fst (𝟙_ (Over S)).hom p = pullback.snd (𝟙_ (Over S)).hom p ≫ p := by
      rw [← pullback.condition]; rfl
    have h2 : (Functor.LaxMonoidal.ε (Over.pullback p)).left ≫ pullback.snd (𝟙_ (Over S)).hom p = 𝟙 _ :=
      Over.w (Functor.LaxMonoidal.ε (Over.pullback p))
    rw [h1, ← Category.assoc, h2, Category.id_comp]
  show (Functor.LaxMonoidal.ε (Over.pullback p) ≫ (Over.pullback p).map η[G]).left ≫ pullback.fst G.hom p = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε]

theorem mem_unitComponent_mul_mem :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left),
      (η[G]).left (G.hom y) ∈ U →
      y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} →
      y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  intro S G _ hsm U y hU hy
  let K := ↑(G.left.residueField y)
  let ω : Spec (CommRingCat.of K) ⟶ G.left := G.left.fromSpecResidueField y
  have hω : ∀ t, ω t = y := fun t => Scheme.fromSpecResidueField_apply y t
  let p : Spec (CommRingCat.of K) ⟶ S := ω ≫ G.hom
  let P := Over.pullback p
  let G' : Over (Spec (CommRingCat.of K)) := P.obj G
  let q : G'.left ⟶ G.left := pullback.fst G.hom p
  have hsm' : Smooth G'.hom := by
    show Smooth (pullback.snd G.hom p); infer_instance
  let y' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G' :=
    Over.homMk (pullback.lift ω (𝟙 _) (by simp [p])) (pullback.lift_snd _ _ _)
  have hy'q : y'.left ≫ q = ω := pullback.lift_fst _ _ _
  have heq : (η[G']).left ≫ q = p ≫ (η[G]).left := overPullback_unit_comp_fst p G
  have hZ := _root_.GlobalTheory.sectionComponents_preimage_of_isPullback G.left S G'.left (Spec (CommRingCat.of K)) G.hom G'.hom p q (η[G]).left (η[G']).left hsm
    (IsPullback.of_hasPullback G.hom p) (Over.w η[G]) (Over.w η[G']) heq
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hy'Z : y'.left pt ∈ connectedComponent ((η[G']).left pt) := by
    have h1 : y'.left pt ∈ q ⁻¹' {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hy'q, hω]; exact hy
    rw [hZ] at h1
    have h2 : G'.hom ⁻¹' {G'.hom (y'.left pt)} = Set.univ := by
      ext t; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    have h3 : G'.hom (y'.left pt) = pt := Subsingleton.elim _ _
    have h1' : y'.left pt ∈ connectedComponentIn (G'.hom ⁻¹' {G'.hom (y'.left pt)}) ((η[G']).left (G'.hom (y'.left pt))) := h1
    rwa [h2, h3, connectedComponentIn_univ] at h1'
  have hU' : (η[G']).left pt ∈ q ⁻¹ᵁ U := by
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, heq, Scheme.Hom.comp_apply]
    have : p pt = G.hom y := by
      show G.hom (ω pt) = _
      rw [hω]
    rw [this]; exact hU
  obtain ⟨z, hz1, hz2⟩ := _root_.GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent K G' hsm' (q ⁻¹ᵁ U) y' hU' hy'Z
  let L : G' ⟶ P.obj (G ⊗ G) := lift (𝟙 G') (toUnit G' ≫ y') ≫ Functor.LaxMonoidal.μ P G G
  have hmap : ∀ {A B : Over S} (f : A ⟶ B), (P.map f).left ≫ pullback.fst B.hom p = pullback.fst A.hom p ≫ f.left := by
    intro A B f; simp [P]
  have key : ∀ (M : G' ⟶ P.obj (G ⊗ G)) {B : Over S} (f : G ⊗ G ⟶ B),
      f.left (pullback.fst (G ⊗ G).hom p (M.left z)) = pullback.fst B.hom p ((M ≫ P.map f).left z) := by
    intro M B f
    rw [Over.comp_left, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (pullback.fst B.hom p), hmap,
      Scheme.Hom.comp_apply]
  refine ⟨pullback.fst (G ⊗ G).hom p (L.left z), ?_, ?_, ?_⟩
  · rw [key L]
    have : L ≫ P.map (fst G G) = 𝟙 G' := by
      show (lift (𝟙 G') (toUnit G' ≫ y') ≫ Functor.LaxMonoidal.μ P G G) ≫ _ = _
      rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
    rw [this, Over.id_left]; exact (Scheme.Hom.mem_preimage _).1 hz1
  · rw [key L]
    have : L ≫ P.map μ[G] = 𝟙 G' * (toUnit G' ≫ y') := by
      show (lift (𝟙 G') (toUnit G' ≫ y') ≫ Functor.LaxMonoidal.μ P G G) ≫ _ = _
      rw [Category.assoc]; rfl
    rw [this]; exact (Scheme.Hom.mem_preimage _).1 hz2
  · rw [key L]
    have : L ≫ P.map (snd G G) = toUnit G' ≫ y' := by
      show (lift (𝟙 G') (toUnit G' ≫ y') ≫ Functor.LaxMonoidal.μ P G G) ≫ _ = _
      rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
    rw [this]
    rw [Over.comp_left, ← Scheme.Hom.comp_apply, Category.assoc]
    show ((toUnit G').left ≫ y'.left ≫ q) z = y
    rw [hy'q]; exact hω _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OToSAlgebraMap
section
noncomputable section

open IsDedekindDomain NumberField Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.AdeleIdem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_tmul_mem {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    (1 : E) ⊗ₜ[F] y ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)

theorem oToS_algebraMap (r : 𝓞 F) :
    ((oToS F E (algebraMap (𝓞 F) (𝓞 E) r) : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) := by
  rw [oToS_coe]
  have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap F E (algebraMap (𝓞 F) F r) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
    ← IsScalarTower.algebraMap_apply]

theorem resS_eq_zero (w : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hw : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal)
    {b : FiniteAdeleRing (𝓞 F) F} (hb : b ∈ intAd F) (hv : b v = 0) :
    resS F w ⟨_, one_tmul_mem hb⟩ = 0 := by
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F d hd0 b hb
  have ev : b v = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) d * y v := by
    rw [e]; rfl
  have hr : r ∈ v.asIdeal := by
    rw [hv] at ev
    have e1 : algebraMap (𝓞 F) (v.adicCompletion F) r = -(algebraMap (𝓞 F) (v.adicCompletion F) d * y v) :=
      eq_neg_of_add_eq_zero_left ev.symm
    have e2 := congrArg Valued.v e1
    rw [Valuation.map_neg, Valuation.map_mul, Formalism.UG.P.csApprox_val_int, Formalism.UG.P.csApprox_val_int] at e2
    rw [← v.intValuation_lt_one_iff_mem] at hd ⊢
    rw [e2]
    have hy1 : Valued.v (y v) ≤ 1 := hy v
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy1) hd
  have hz : ∀ x ∈ v.asIdeal, resS F w (oToS F E (algebraMap (𝓞 F) (𝓞 E) x)) = 0 := by
    intro x hx
    rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hw] at hx
    exact hx
  have key : (⟨_, one_tmul_mem hb⟩ : Formalism.L2.Herm.intAf F E) =
      oToS F E (algebraMap (𝓞 F) (𝓞 E) r) + oToS F E (algebraMap (𝓞 F) (𝓞 E) d) * ⟨_, one_tmul_mem hy⟩ := by
    apply Subtype.ext
    rw [Subring.coe_add, Subring.coe_mul, oToS_algebraMap, oToS_algebraMap]
    show (1 : E) ⊗ₜ[F] b = _ + _ * (1 : E) ⊗ₜ[F] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
  rw [key, map_add (f := _), map_mul, hz r hr, hz d hd, zero_mul, add_zero]


open Classical in
def ind (S : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if v ∈ S then 1 else 0) ∈ v.adicCompletionIntegers F
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
theorem ind_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    ind S v = if v ∈ S then 1 else 0 := rfl

theorem ind_mem (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S ∈ intAd F := by
  intro v
  show ind S v ∈ v.adicCompletionIntegers F
  rw [ind_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

end GlobalTheory.AdeleIdem
end
end

