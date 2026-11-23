module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalProperty
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.AcrUniv

theorem pow_mem_map {R B : Type} [CommRing R] [CommRing B] (h : R →+* B) (I : Ideal R) (p : ℕ) (hp : p.Prime)
    (hI : ∀ x ∈ I, x ^ p ∈ Ideal.span {(p : R)}) : ∀ x ∈ I.map h, x ^ p ∈ Ideal.span {(p : B)} := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => x ^ p ∈ Ideal.span {(p : B)}) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hI y hy)
    rw [← map_pow, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [zero_pow hp.ne_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
    rw [hr]
    exact add_mem (add_mem ha hb) (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))))
  · intro a b _ hb
    rw [smul_eq_mul, mul_pow]
    exact Ideal.mul_mem_left _ _ hb

section Tens

variable {R S T C B : Type} [CommRing R] [CommRing S] [CommRing T] [CommRing C] [CommRing B]
  [Algebra R S] [Algebra R T] [Algebra R C] [Algebra S C] [Algebra T C]
  [IsScalarTower R S C] [IsScalarTower R T C]


open TensorProduct in
theorem tens_ext
    (hs : Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)))
    (f f' : C →+* B) (h1 : ∀ s, f (algebraMap S C s) = f' (algebraMap S C s))
    (h2 : ∀ t, f (algebraMap T C t) = f' (algebraMap T C t)) : f = f' := by
  refine RingHom.ext fun c => ?_
  obtain ⟨z, rfl⟩ := hs c
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [Algebra.TensorProduct.lift_tmul, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom',
      map_mul, map_mul, h1, h2]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]


open TensorProduct in
theorem tens_desc (m n : ℕ)
    (hs : Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)))
    (hk : ∀ z : S ⊗[R] T, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _) z = 0 ↔
        z ∈ Ideal.span {(m : S ⊗[R] T) ^ n})
    (u : S →+* B) (v : T →+* B) (huv : ∀ r, u (algebraMap R S r) = v (algebraMap R T r))
    (hm : (m : B) ^ n = 0) :
    ∃ f : C →+* B, (∀ s, f (algebraMap S C s) = u s) ∧ ∀ t, f (algebraMap T C t) = v t := by
  letI : Algebra R B := (u.comp (algebraMap R S)).toAlgebra
  let u' : S →ₐ[R] B := { u with commutes' := fun _ => rfl }
  let v' : T →ₐ[R] B := { v with commutes' := fun r => (huv r).symm }
  let L : S ⊗[R] T →ₐ[R] B := Algebra.TensorProduct.lift u' v' (fun _ _ => Commute.all _ _)
  let Φ : S ⊗[R] T →ₐ[R] C := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
    (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)
  have hker : RingHom.ker (Φ : S ⊗[R] T →+* C) ≤ RingHom.ker (L : S ⊗[R] T →+* B) := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((hk z).1 hz)
    rw [RingHom.mem_ker, map_mul, map_pow, map_natCast, hm, mul_zero]
  let f : C →+* B := (Φ : S ⊗[R] T →+* C).liftOfSurjective hs ⟨(L : S ⊗[R] T →+* B), hker⟩
  have hf : ∀ z, f (Φ z) = L z := fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z
  refine ⟨f, fun s => ?_, fun t => ?_⟩
  · have h := hf (s ⊗ₜ 1)
    simpa [Φ, L, u'] using h
  · have h := hf (1 ⊗ₜ t)
    simpa [Φ, L, v'] using h

end Tens

end GlobalTheory.CompanionTheory.AcrUniv

namespace GlobalTheory.CompanionTheory.AcrUniv

theorem maps_out : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (B : Type) [CommRing B] (h : (base l).Acr n →+* B), (∀ g : A.A →+* B ⧸ ((base l).PFil n).map h, (∀ a : Ob l, g (A.s a) = Ideal.Quotient.mk _ (h ((base l).toAcr n (WittVector.teichmuller l a)))) → ∃ f : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h ∧ ∀ a, Ideal.Quotient.mk _ (f (A.toAcr n (WittVector.teichmuller l a))) = g a) ∧ ∀ f f' : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h → f'.comp (mapAcr A.fromBase n) = h → (∀ a, f (A.toAcr n (WittVector.teichmuller l a)) - f' (A.toAcr n (WittVector.teichmuller l a)) ∈ ((base l).PFil n).map h) → f = f' := by
  intro l _ A n B _ h
  have hp : l.Prime := Fact.out
  obtain ⟨⟨π, -, -⟩, hFil, -, -, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.AcrMod.acr_modp A n
  obtain ⟨-, -, -, -, -, hpow, -⟩ := _root_.GlobalTheory.CompanionTheory.AcrMod.acr_modp (base l) n
  have hlB : (l : B) ^ n = 0 := by
    rw [← map_natCast h, ← map_pow, pow_l_acr, map_zero]
  have hlJ : (l : B) ∈ ((base l).PFil n).map h := by
    rw [← map_natCast h]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hJp : ∀ x ∈ ((base l).PFil n).map h, x ^ l ∈ Ideal.span {(l : B)} :=
    pow_mem_map h _ l hp fun x hx => (hpow x hx).2
  have hOb : D.Pf l (Ob l) := ⟨(base l).natCast_l, (base l).perf.1⟩
  have hA : D.Pf l A.A := ⟨A.natCast_l, A.perf.1⟩
  obtain ⟨hts, htk⟩ := RL.tens A n
  have hbs := ((RL.base_acr (base l) isBase_base).2 n).1
  refine ⟨fun g hg => ?_, fun f f' h1 h2 h3 => ?_⟩
  · obtain ⟨⟨f₀, hf₀⟩, -⟩ := GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l _ n hA hlB hlJ hJp g
    have hc : f₀.comp A.sW = h.comp ((base l).toAcr n) :=
      (GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l (A := Ob l) _ n hOb hlB hlJ hJp (g.comp A.s)).2 _ _ fun a => by
        rw [RingHom.comp_apply, RingHom.comp_apply, sW, WittVector.map_teichmuller, hf₀]
        exact hg a
    have huv : ∀ r : Ainf l, (h.comp ((base l).cris n)) (algebraMap (Ainf l) (Acris l) r) =
        f₀ (algebraMap (Ainf l) A.W r) := fun r => by
      rw [RingHom.comp_apply, cris_algebraMap]
      have e : (base l).sW r = r := wmap_id r
      rw [e]
      exact (RingHom.congr_fun hc r).symm
    obtain ⟨f, hf1, hf2⟩ := tens_desc l n hts htk (h.comp ((base l).cris n)) f₀ huv hlB
    refine ⟨f, RingHom.ext fun y => ?_, fun a => ?_⟩
    · obtain ⟨a, rfl⟩ := hbs y
      rw [RingHom.comp_apply, mapAcr_cris]
      exact hf1 a
    · have e : f (A.toAcr n (WittVector.teichmuller l a)) = f₀ (WittVector.teichmuller l a) :=
        hf2 (WittVector.teichmuller l a)
      rw [e, hf₀]
  · have hfJ : A.PFil n ≤ (((base l).PFil n).map h).comap f := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
        exact hlJ
      · rw [hFil 1, Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_comap, ← RingHom.comp_apply, h1]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right hx)
    have hw := (GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l _ n hA hlB hlJ hJp
      ((Ideal.quotientMap _ f hfJ).comp π)).2 (f.comp (A.toAcr n)) (f'.comp (A.toAcr n))
      fun a => Ideal.Quotient.eq.2 (h3 a)
    refine tens_ext hts f f' (fun a => ?_) fun t => RingHom.congr_fun hw t
    have e : algebraMap (Acris l) (A.Acr n) a = mapAcr A.fromBase n ((base l).cris n a) :=
      (mapAcr_cris A.fromBase n a).symm
    rw [e]
    exact RingHom.congr_fun (h1.trans h2.symm) _

end GlobalTheory.CompanionTheory.AcrUniv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheaves
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Union

theorem support_inf_subset {X : Scheme.{0}} (T₁ T₂ : X.IdealSheafData) :
    ((T₁ ⊓ T₂).support : Set X) ⊆ (T₁.support : Set X) ∪ T₂.support := by
  have hle : T₁ * T₂ ≤ T₁ ⊓ T₂ := fun U => Ideal.mul_le_inf
  have h := Scheme.IdealSheafData.support_antitone hle
  intro x hx
  have hx' : x ∈ (T₁ * T₂).support := h hx
  rw [Scheme.IdealSheafData.support_mul] at hx'
  exact hx'

theorem universallyClosed_of_cover {Z₁ Z₂ Z S : Scheme.{0}} (p₁ : Z₁ ⟶ Z) (p₂ : Z₂ ⟶ Z)
    (h : Z ⟶ S) (h₁ : UniversallyClosed (p₁ ≫ h)) (h₂ : UniversallyClosed (p₂ ≫ h))
    (hc : ∀ z : Z, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂) : UniversallyClosed h := by
  rw [universallyClosed_iff]
  intro X' Y' i₁ i₂ f' H
  have key : ∀ {W : Scheme.{0}} (p : W ⟶ Z), UniversallyClosed (p ≫ h) →
      IsClosedMap (pullback.fst i₁ p ≫ f') := by
    intro W p hp
    have H' : IsPullback (pullback.fst i₁ p ≫ f') (pullback.snd i₁ p) i₂ (p ≫ h) :=
      (IsPullback.of_hasPullback i₁ p).paste_horiz H
    exact (universallyClosed_iff _).mp hp _ _ _ H'
  have lift : ∀ {W : Scheme.{0}} (p : W ⟶ Z) (x : X'), i₁ x ∈ Set.range p →
      ∃ z : ↑(pullback i₁ p), pullback.fst i₁ p z = x := by
    rintro W p x ⟨w, hw⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
    exact ⟨z, hz⟩
  show IsClosedMap f'
  intro C hC
  have hEq : f' '' C = (pullback.fst i₁ p₁ ≫ f') '' (pullback.fst i₁ p₁ ⁻¹' C) ∪
      (pullback.fst i₁ p₂ ≫ f') '' (pullback.fst i₁ p₂ ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hc (i₁ x) with hr | hr
      · obtain ⟨z, hz⟩ := lift p₁ x hr
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz⟩ := lift p₂ x hr
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨_, hz, by simp⟩
      · exact ⟨_, hz, by simp⟩
  rw [hEq]
  exact (key p₁ h₁ _ (hC.preimage (pullback.fst i₁ p₁).continuous)).union
    (key p₂ h₂ _ (hC.preimage (pullback.fst i₁ p₂).continuous))

theorem isProper_inf : ∀ {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    (T₁ T₂ : X.IdealSheafData), IsProper (T₁.subschemeι ≫ f) → IsProper (T₂.subschemeι ≫ f) →
    IsProper ((T₁ ⊓ T₂).subschemeι ≫ f) := by
  intro X S f _ _ T₁ T₂ hT₁ hT₂
  let K : X.IdealSheafData := T₁ ⊓ T₂
  let p₁ : T₁.subscheme ⟶ K.subscheme := IsClosedImmersion.lift K.subschemeι T₁.subschemeι
    (by simpa [K] using (inf_le_left : T₁ ⊓ T₂ ≤ T₁))
  let p₂ : T₂.subscheme ⟶ K.subscheme := IsClosedImmersion.lift K.subschemeι T₂.subschemeι
    (by simpa [K] using (inf_le_right : T₁ ⊓ T₂ ≤ T₂))
  have e₁ : p₁ ≫ K.subschemeι = T₁.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have e₂ : p₂ ≫ K.subschemeι = T₂.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have u₁ : UniversallyClosed (p₁ ≫ K.subschemeι ≫ f) := by
    rw [← Category.assoc, e₁]; infer_instance
  have u₂ : UniversallyClosed (p₂ ≫ K.subschemeι ≫ f) := by
    rw [← Category.assoc, e₂]; infer_instance
  have cover : ∀ {T : X.IdealSheafData} (p : T.subscheme ⟶ K.subscheme),
      p ≫ K.subschemeι = T.subschemeι → ∀ z : K.subscheme, K.subschemeι z ∈ (T.support : Set X) →
      z ∈ Set.range p := by
    intro T p e z hz
    obtain ⟨w, hw⟩ := T.range_subschemeι.ge hz
    refine ⟨w, K.subschemeι.isEmbedding.injective ?_⟩
    rw [← hw, ← e]
    rfl
  have hc : ∀ z : K.subscheme, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂ := by
    intro z
    have hz : K.subschemeι z ∈ (K.support : Set X) := K.range_subschemeι.le ⟨z, rfl⟩
    rcases support_inf_subset T₁ T₂ hz with h | h
    · exact Or.inl (cover p₁ e₁ z h)
    · exact Or.inr (cover p₂ e₂ z h)
  have : UniversallyClosed (K.subschemeι ≫ f) :=
    universallyClosed_of_cover p₁ p₂ _ u₁ u₂ hc
  exact ⟨⟩

end GlobalTheory.CompanionTheory.GE.Union
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullFrob
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.CrysPhi

theorem pull_frob {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {σ : b.R →+* b.R} {τ : Λ →+* Λ}
    (mo : GlobalTheory.LogCris.Mor (F.cr b ht κ) (F.cr b ht κ) σ) (h : ∀ a, σ (c a) = c (τ a))
    {C' : Type 1} [Category.{0} C'] {F' : C' ⥤ ModuleCat.{0} Λ}
    (Bm : CH.Mor (OM (F.cr b ht κ) c) F' (RingHom.id Λ)) (Ph : CH.Mor F' F' τ)
    (η : ∀ T, Bm.G.obj (Ph.G.obj T) ⟶ mo.obj (Bm.G.obj T))
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (Bm.G.obj (Ph.G.obj T)).B),
      (η T').φ ((Bm.G.map (Ph.G.map f)).φ x) = (Bm.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (Bm.G.obj (Ph.G.obj T)).B), Bm.τ T ((η T).φ x) = Ph.τ T (Bm.τ (Ph.G.obj T) x))
    (j : ℕ) (x : CH.H (OM (F.cr b ht κ) c) j) :
    Bm.pull j ((omMor mo τ h).pull j x) = Ph.pull j (Bm.pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact (cr_pull_eq (Bm.comp Ph) ((omMor mo τ h).comp Bm) η nat hτ j x).symm

theorem qmap_frb {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] (J : Ideal A) (ph : A →+* A)
    (hl : (l : A ⧸ J) = 0) (hq : J ≤ J.comap ph)
    (hm : ∀ r, Ideal.Quotient.mk J (ph r) = Ideal.Quotient.mk J r ^ l) :
    Ideal.quotientMap J ph hq = frb hl :=
  Ideal.Quotient.ringHom_ext (RingHom.ext hm)

theorem pt_frb {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) {A : Type} [CommRing A] (J : Ideal A) (ph : A →+* A)
    (hl : (l : A ⧸ J) = 0) (hq : J ≤ J.comap ph)
    (hm : ∀ r, Ideal.Quotient.mk J (ph r) = Ideal.Quotient.mk J r ^ l) (z : F.Pt.obj (CommRingCat.of (A ⧸ J))) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap J ph hq)) z = F.Pt.map (CommRingCat.ofHom (frb hl)) z := by
  rw [qmap_frb J ph hl hq hm]

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def etaPhi (n : ℕ) (T : El (F.pt κ)) :
    (gT F κ true n).obj T ⟶ (SH.phiM F κ n).obj ((gT F κ true n).obj T) :=
  crHom (T := (gT F κ true n).obj T) (T' := (SH.phiM F κ n).obj ((gT F κ true n).obj T)) (((elπ (F.pt κ)).obj T).phi n)
    (fun r => (mapAcr_phi ((elπ (F.pt κ)).obj T).fromBase n r).symm) (((elπ (F.pt κ)).obj T).dpP_phi n) fun h => by
      exact pt_frb F (((elπ (F.pt κ)).obj T).PFil n) (((elπ (F.pt κ)).obj T).phi n)
        (l_zero ((gT F κ true n).obj T).y.1.1) h (phi_mk _ n) _

theorem phi_beta (n j : ℕ) (x : Hc F κ true n j) :
    β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x) :=
  pull_frob (SH.phiM F κ n) ((base l).phi_cris n) (βMor F κ true n) (phiMor (F.pt κ) n) (etaPhi F κ n)
    (fun f x => (mapAcr_phi ((elπ (F.pt κ)).map f) n x).symm) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.CrysPhi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRetype
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.RedNat

universe w w' v u v' u'

section Retype
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ σ₂ : R →+* R'}

def retype (m : CH.Mor F F' σ) (σ₂ : R →+* R') (h : ∀ T (a : R) (y : F'.obj T), σ a • y = σ₂ a • y) : CH.Mor F F' σ₂ where
  G := m.G
  τ T :=
    { toFun := m.τ T
      map_add' := map_add _
      map_smul' := fun a x => (LinearMap.map_smulₛₗ (m.τ T) a x).trans (h T a _) }
  nat := m.nat

theorem pull_retype (m : CH.Mor F F' σ) (h : ∀ T (a : R) (y : F'.obj T), σ a • y = σ₂ a • y) (n : ℕ) (x : CH.H F n) :
    (retype m σ₂ h).pull n x = m.pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
  have hb : CH.d F' n (m.pullC n a) = 0 := by rw [CH.Mor.d_pullC]; exact (congrArg _ ha).trans (map_zero _)
  exact (CrystallineSemistableComparison.P.mapH_cls (retype m σ₂ h).hom n a ha hb).trans (CrystallineSemistableComparison.P.mapH_cls m.hom n a ha hb).symm

end Retype

section Eta
variable {O A₁ A₂ R₁ R₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n s : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ')

theorem eta_comm (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x))
    (T : Thick (nlFun γ₂ 0 X₂ q₂ (κA O I₂))) (r : R₁) :
    iBar ((nm.mor 0).obj T) l n (d₁.ρ r) = iBar T l n (d₂.ρ (σ' r)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d₁.ρ r)
  rw [hρ, ← ha]
  rfl

def etaR (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u)
    (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x))
    (T : Thick (nlFun γ₂ 0 X₂ q₂ (κA O I₂))) (h₁ : TF l s ((nm.mor 0).obj T)) (h₂ : TF l s T) :
    redObj ((nm.mor 0).obj T) d₁ h₁ ⟶ m.obj (redObj T d₂ h₂) :=
  mkH (show T.B ⧸ lnT T l n →+* T.B ⧸ lnT T l n from RingHom.id _) (fun r => eta_comm d₁ d₂ nm hρ T r)
    ⟨le_of_eq (Ideal.map_id _), fun x hx => rfl⟩ (fun x hx => hx) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        have hw1 := (redObj ((nm.mor 0).obj T) d₁ h₁).w r
        have hw2 := (m.obj (redObj T d₂ h₂)).w r
        have h3 : Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J ((redObj ((nm.mor 0).obj T) d₁ h₁).i r) =
            Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J ((m.obj (redObj T d₂ h₂)).i r) :=
          congrArg (Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J) (eta_comm d₁ d₂ nm hρ T r)
        exact (congrArg (Ideal.quotientMap (m.obj (redObj T d₂ h₂)).J
          (show T.B ⧸ lnT T l n →+* T.B ⧸ lnT T l n from RingHom.id _) (fun x hx => hx)) hw1).trans (h3.trans hw2.symm)
      · have e := hpt _ (redObj T d₂ h₂).y
        refine Eq.trans ?_ e.symm
        change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (qBar ((nm.mor 0).obj T) l n)) ≫ (pt T ≫ nm.u) =
          (Spec.map (CommRingCat.ofHom (qBar T l n)) ≫ pt T) ≫ nm.u
        rw [Category.assoc, ← Category.assoc, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

end Eta

section Main
variable {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a))


include hc₁ hc₂ h₀ in
theorem lam_mem (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) (a : Λ₁) :
    σ (lam₁ a) - lam₂ (σ₀ a) ∈ Ideal.span {(l : A₂) ^ n} := by
  refine Ideal.Quotient.eq.1 ?_
  have e := hρ (c₁ a)
  rw [h₀, hc₂, hc₁] at e
  exact e.symm


include hc₁ hc₂ h₀ in
theorem lam_smul (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) (r : Option ℤ)
    (T : (TS γ₂ q₂ l s {⊤}).FullSubcategory) (a : Λ₁)
    (y : (sq (IdF.top (sP (TS γ₂ q₂ l s {⊤})).A) (stdI (TS γ₂ q₂ l s {⊤}) r ((l : A₂) ^ n))).obj T) :
    (σ.comp lam₁) a • y = (lam₂.comp σ₀) a • y := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext (Ideal.Quotient.eq.2 ?_)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (lam_mem d₁ d₂ c₁ c₂ lam₁ lam₂ hc₁ hc₂ σ₀ h₀ hρ a)
  refine ln_le q₂ s {⊤} r T ?_
  change T.obj.i (σ (lam₁ a)) * (show T.obj.B from b) - T.obj.i (lam₂ (σ₀ a)) * (show T.obj.B from b) ∈ lnT T.obj l n
  rw [← sub_mul, ← map_sub, ← hz, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

end Main

theorem red_nm : ∀ {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u) →
    (∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X₁ q₁ κ₁) c₁) j),
    (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r).pull j ((B.omMor m σ₀ h₀).pull j x) =
      nmHM nm l s r n j ((redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).pull j x) := by
  intro O A₁ A₂ R₁ R₂ Λ₁ Λ₂ _ _ _ _ _ _ _ _ _ I₁ I₂ γ₁ γ₂ J₁ J₂ δ₁ δ₂ κ₁ κ₂ l n d₁ d₂ X₁ X₂ q₁ q₂ s σ nm σ' m c₁ c₂ lam₁ lam₂
    hc₁ hc₂ σ₀ h₀ hpt hρ r j x
  let S2 := (nmS nm l s).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (nm_std nm l s r n)
  letI t1 : RingHomCompTriple σ₀ lam₂ (lam₂.comp σ₀) := ⟨rfl⟩
  letI t2 : RingHomCompTriple lam₁ σ (σ.comp lam₁) := ⟨rfl⟩
  let M1 : CH.Mor _ _ (lam₂.comp σ₀) := (B.omMor m σ₀ h₀).comp (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r)
  let M2 : CH.Mor _ _ (σ.comp lam₁) := (redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).comp S2
  have hsc := lam_smul (q₂ := q₂) d₁ d₂ s c₁ c₂ lam₁ lam₂ hc₁ hc₂ σ₀ h₀ hρ r
  have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := lam₂.comp σ₀) (B.omMor m σ₀ h₀) (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r) j x).1
  have h2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := σ.comp lam₁) (redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r) S2 j x).1
  have h3 := pull_retype M2 (σ₂ := lam₂.comp σ₀) hsc j x
  let η : (retype M2 (lam₂.comp σ₀) hsc).G ⟶ M1.G :=
    { app := fun T => etaR d₁ d₂ nm m hpt hρ T.obj T.property.1 T.property.1
      naturality := fun T T' f => hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)) }
  have h4 := CrystallineSemistableComparison.P.prism (retype M2 (lam₂.comp σ₀) hsc) M1 η (fun T y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) y
    rfl) j x
  exact h1.symm.trans (h4.symm.trans (h3.trans h2))

end GlobalTheory.CompanionTheory.RedNat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedCmp
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisCmp

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redMk (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

def cmpMk (n : ℕ) : Mor (Lc F κ false n) (Lc F κ true n) (RingHom.id _) :=
  B.crMor (F := F) (F' := F) (b := bs l false n) (b' := bs l true n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    ((base l).dp_fil_pfil n) (basePt F (Ideal.Quotient.factor le_sup_right) rfl) fun _ _ _ => rfl

theorem fac_κb (n : ℕ) :
    (Ideal.Quotient.factor (S := JJ false (base l) n) (T := JJ true (base l) n) le_sup_right).comp (κb κ false n) = κb κ true n := rfl

theorem cmp_pt {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((cmpMk F κ m).pt.app B₀ ((redMk F κ true h).pt.app B₀ y)).1.2 =
      ((redMk F κ false h).pt.app B₀ ((cmpMk F κ n).pt.app B₀ y)).1.2 :=
  SH.base_base F (κ₁ := κb κ false m) (κ₂ := κb κ true m) (κ₃ := κb κ false n) (κ₄ := κb κ true n)
    (fac_κb κ m) (red_κb κ true h) (red_κb κ false h) (fac_κb κ n) B₀ y

theorem red_cmp {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j) :
    redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) := by
  unfold redHc redMor cmpMor
  exact cr_square (cmpMk F κ m) (redMk F κ true h) (redMk F κ false h) (cmpMk F κ n) (SH.idc _)
    (red_cris _ h) (red_cris _ h) (SH.idc _) (fun r => (SH.idc ((base l).red h) r).symm)
    (cmp_pt F κ h) j x

theorem main : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ false m j), redHc F κ true h j ((cmpMor F κ m).pull j x) = (cmpMor F κ n).pull j (redHc F κ false h j x) :=
  fun F κ _ _ h j x => red_cmp F κ h j x

end GlobalTheory.CompanionTheory.CrisCmp
end
end

