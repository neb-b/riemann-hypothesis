module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHopWord
section
set_option autoImplicit false

noncomputable section

open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open UpperTheory.Gal.G3 (Tower Th)

variable {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ] (X : Tower B Γ) (T : Th.{0} B ℂ)

private theorem hecke_zero (hL : UpperTheory.Gal.G3.HopLin.{0}) (hT : T.Good) (j : X.ι) (hz : X.IsFn j (0 : Γ → ℂ)) :
    X.hecke T j 0 = 0 := by
  have h := (hL X T hT j 0 0 0 hz hz).2
  simpa using h

private theorem hecke_sum (hL : UpperTheory.Gal.G3.HopLin.{0}) (hT : T.Good) (j : X.ι) (hz : X.IsFn j (0 : Γ → ℂ))
    (hadd : ∀ f f' : Γ → ℂ, X.IsFn j f → X.IsFn j f' → X.IsFn j (f + f'))
    (hsm : ∀ (c : ℂ) (f : Γ → ℂ), X.IsFn j f → X.IsFn j (c • f))
    {I : Type} (s : Finset I) (f : I → Γ → ℂ) (c : I → ℂ) (hf : ∀ i ∈ s, X.IsFn j (f i)) :
    X.IsFn j (∑ i ∈ s, c i • f i) ∧ X.hecke T j (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • X.hecke T j (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using hz, by simpa using hecke_zero X T hL hT j hz⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h3 := hsm (c a) (f a) (hf a (Finset.mem_insert_self a s))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨hadd _ _ h3 h1, ?_⟩
    rw [(hL X T hT j _ _ 0 h3 h1).1, h2,
      (hL X T hT j (f a) (f a) (c a) (hf a (Finset.mem_insert_self a s)) (hf a (Finset.mem_insert_self a s))).2]

end UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.hopWord_of :
    UpperTheory.Gal.G3.FnRing → UpperTheory.Gal.G3.HopLin.{0} → UpperTheory.Gal.G3.HopMul.{0} → HopWord := by
  intro hR hL hM B Γ _ X T hT j
  obtain ⟨-, hz, hfg, hsm⟩ := hR X ℂ j
  have hadd : ∀ f f' : Γ → ℂ, X.IsFn j f → X.IsFn j f' → X.IsFn j (f + f') := fun f f' a b => (hfg f f' a b).1
  refine ⟨fun m f c hf => hecke_sum X T hL hT j hz hadd hsm Finset.univ f c fun i _ => hf i, ?_⟩
  intro J ψ f hψ hf
  have hw : ∀ w : List J, X.IsFn j (wordFn (X.K j) ψ w f) ∧
      X.hecke T j (wordFn (X.K j) ψ w f) = (w.map fun i => X.hecke T j (ψ i)).prod * X.hecke T j f := by
    intro w
    induction w with
    | nil => exact ⟨hf, by simp [wordFn]⟩
    | cons i w ih =>
      obtain ⟨h1, h2⟩ := ih
      have e : wordFn (X.K j) ψ (i :: w) f = UpperTheory.Gal.G3.conv (X.K j) (ψ i) (wordFn (X.K j) ψ w f) := rfl
      rw [e]
      refine ⟨(hfg _ _ (hψ i) h1).2, ?_⟩
      rw [hM X T hT j _ _ (hψ i) h1, h2, List.map_cons, List.prod_cons, mul_assoc]
  refine ⟨hw, fun s => ?_⟩
  have hs := hecke_sum X T hL hT j hz hadd hsm s.support (fun w => wordFn (X.K j) ψ w f) s fun w _ => (hw w).1
  have e : polyFn (X.K j) ψ s f = ∑ w ∈ s.support, s w • wordFn (X.K j) ψ w f := rfl
  rw [e]
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  unfold UpperTheory.Gal.CertificateRingHomMap.wop Finsupp.sum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [(hw w).2, smul_mul_assoc]

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKSHodge
section
open UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Gal.Int.Geo in
theorem UpperTheory.Gal.LocalSmoothExtension.kSHodge_of :
    HodgeEig → KSBc → SpecConj → MemOp → FnDecomp → OccOf → UpperTheory.Gal.Int.Geo.KSHodge := by
  intro hE hB hS hM hF hO p _ D G L sc lam anti
  obtain ⟨k, hk⟩ := hE p D G L sc lam anti
  refine ⟨k, ?_⟩
  intro R _ _ gb T N J g θ f hf hs τ hρ ht σ i₀ h hh i
  let gb' : GBase D.toG ℂ :=
    { ρ := D.ρc
      ρ_root := D.toG.ρc_root
      t := fun i => (D.toG.tau i).comp (algebraMap _ _)
      t_ω := fun i => D.toG.tau_ω i
      comax := fun i j hij => by
        have ha : D.toG.a = 1 := sc.a1
        exact absurd (Fin.ext (by have := i.2; have := j.2; omega)) hij }
  have hstd : StdC D gb' := ⟨rfl, fun _ _ => rfl⟩
  obtain ⟨⟨X', lev', c1, c2, c3, c4, c5, c6⟩, hX, hl⟩ :=
    hB p D G L R gb k T τ gb' hρ.symm (fun i c => (ht i c).symm)
  dsimp only at hX
  subst hX
  cases hl
  have e : (fun (j : J) (y : G.GAf) => σ ((g j).fn y)) = fun j => (g j).fn := by
    funext j y
    exact map_natCast σ _
  have h1 := hS σ p D G L lam (L.KN N.1) J (fun j => (g j).fn) θ f hs
  rw [e] at h1
  have hfn : T.X.IsFn (T.lev N) f := by
    refine (hF _ _ T.X (T.lev N) f).2 ?_ ?_
    · rw [T.K_eq]; exact hf.1
    · intro y hy
      exact (T.Δ_eq _).2 (hf.2 y hy)
  have hfn' : T.X.IsFn (T.lev N) fun y => σ (f y) := by
    obtain ⟨a1, a2, a3⟩ := hfn
    refine ⟨fun k hk y => ⟨?_, ?_⟩, fun y hy => a2 y ?_, a3.subset fun y hy => ?_⟩
    · show σ _ = σ _
      rw [(a1 k hk y).1]
    · show σ _ = σ _
      rw [(a1 k hk y).2]
    · exact fun h0 => hy (by show σ (f y) = 0; rw [h0, map_zero])
    · exact fun h0 => hy (by show σ (f y.out) = 0; rw [h0, map_zero])
  obtain ⟨b, x, hx, hx'⟩ := hk gb' hstd ⟨_, T.lev, c1, c2, c3, c4, c5, c6⟩ N σ i₀ h hh J (fun j => (g j).fn)
    (fun j => σ (θ j)) (fun y => σ (f y)) (fun j => (hM p D G L R gb k T N J g j).1) hfn' h1 i
  exact hO p D G L R gb k T N J g τ _ (h i) b x hx hx'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.POccOf
section
open UpperTheory.Gal.LocalSmoothExtension

set_option maxHeartbeats 1000000 in
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.HodgeCoh in
theorem UpperTheory.Gal.LocalSmoothExtension.occOf_of :
    MemOp → UpperTheory.Gal.G3.HodgeGood → UpperTheory.Gal.G3.HodgeTr → UpperTheory.Gal.G3.BcGood.{0} → UpperTheory.Gal.G3.OpBc.{0} → UpperTheory.Gal.G3.OpTr.{0} → UpperTheory.Gal.G3.BcSplits → OccOf := by
  intro memop hg htr bcg opbc optr bcs p _ D G L R _ _ gb k T N J g τ θ a b x hx hxe
  letI : Algebra R ℂ := τ.toAlgebra
  refine ⟨b, x, hx, fun j => ?_⟩
  obtain ⟨-, hfin, het, hop⟩ := memop p D G L R gb k T N J g j
  haveI := hfin
  haveI := het
  have hΘ := bcg (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (hg ℂ a b)
  have hs : (T.tower N g).s j ≫ (T.tower N g).q = (T.tower N g).s j ≫ (T.tower N g).q := rfl
  have h2 := opbc (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) (T.tower N g).q ((T.tower N g).s j) ((T.tower N g).t j) hs
    ((T.tower N g).comm j) _ (hop _ hΘ)
  obtain ⟨hf', he', -⟩ := bcs (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j) hs
    ((T.tower N g).s j) hs PEmpty (fun e => e.elim) (fun e => e.elim)
  haveI := hf'
  haveI := he'
  have ht' : UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).t j) ((T.tower N g).comm j) ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) := by
    unfold UpperTheory.Gal.G3.bcMap
    rw [pullback.lift_snd, pullback.lift_snd]
  have htr' := htr ℂ a b (pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ))) _
    (UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs) rfl
  have hA := (optr (UpperTheory.Gal.G3.hodge ℂ a b) (hg ℂ a b) _ _ _ _ _ rfl ht' _ htr' _).1 h2
  have e1 : (UpperTheory.Gal.Int.Geo.bcAlong (T.tower N g) τ).s j =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs := rfl
  refine ⟨e1 ▸ hf', e1 ▸ he', Eq.trans ?_ (hxe j)⟩
  rw [hA]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.Gen.BaseChange (down)
open GlobalTheory.GalV (Splits)
open UpperTheory.Gal.Int.Geo (KS Lv Mem IsTrans TIso)

namespace UpperTheory.Gal.LocalSmoothExtension

def MapEq : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R)
    (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : GObj b N s₁) (o₂ : GObj b N s₂) (o₃ : GObj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃)
    (m₂ : GObjMap o₂ o₃ g),
    (∀ m₁ : GObjMap o₁ o₂ f, ∃ n : GObjMap o₁ o₃ (f ≫ g), n.φ = m₁.φ ≫ m₂.φ) ∧
    ∀ m : GObjMap o₁ o₃ (f ≫ g), ∃ n : GObjMap o₁ o₂ f, n.φ ≫ m₂.φ = m.φ

def ModelBc : Prop :=
  ∀ (G : GDatum) (R₁ R₂ : Type) [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂] (τ : R₁ →+* R₂) (gb₁ : GBase G R₁)
    (gb₂ : GBase G R₂) (hρ : gb₂.ρ = τ gb₁.ρ) (ht : ∀ i, gb₂.t i = τ.comp (gb₁.t i)) (N : ℕ) (M : GenModel gb₁ N),
    ∃ (M' : GenModel gb₂ N) (f : M'.X ⟶ M.X), IsPullback f M'.s M.s (spMap τ) ∧
      Nonempty (GObjMap (down hρ ht rfl M'.univ) M.univ f)

def HomEx : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R)
    (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f),
    (∀ ψ : o'.A ⟶ o''.A, IsMonHom ψ → ∃ ψ₁ : o₁'.A ⟶ o₁''.A, IsMonHom ψ₁ ∧ ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left) ∧
    (∀ ψ₁ ψ₂ : o₁'.A ⟶ o₁''.A, ψ₁.left ≫ m''.φ = ψ₂.left ≫ m''.φ → ψ₁ = ψ₂) ∧
    ∀ d : ℕ, ((𝟙 o₁'.A) ^ d).left ≫ m'.φ = m'.φ ≫ ((𝟙 o'.A) ^ d).left

def PolPull : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R)
    (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f) (ψ : o'.A ⟶ o''.A) (ψ₁ : o₁'.A ⟶ o₁''.A),
    ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left → ∀ c : ℕ, Nonempty (LBIso (Hecke.lbPow o'.P c) (o''.P.pull (Hecke.sq2 ψ))) →
      Nonempty (LBIso (Hecke.lbPow o₁'.P c) (o₁''.P.pull (Hecke.sq2 ψ₁)))

def TatePull : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase D.toG R) (N : ℕ) (S S₁ : Scheme.{0})
    (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o : GObj b N s) (o₁ : GObj b N s₁) (m : GObjMap o₁ o f)
    (k : Type) [Field k] (t : Sp k ⟶ S₁) (I : TIso o (t ≫ f)),
    ∃ I₁ : TIso o₁ t, ∀ n y, (I₁.ev n y).left ≫ m.φ = (I.ev n y).left

def TransPull : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
    (b : GBase D.toG R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S), f ≫ s = s₁ →
    ∀ (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f) (h : G.GAf) (ψ : o'.A ⟶ o''.A), IsTrans L h o' o'' ψ →
      ∃ ψ₁ : o₁'.A ⟶ o₁''.A, ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left ∧ IsTrans L h o₁' o₁'' ψ₁

def LegBc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R₁ R₂ : Type) [CommRing R₁] [CommRing R₂]
    [Algebra ℚ R₁] [Algebra ℚ R₂] (τ : R₁ →+* R₂) (gb₁ : GBase D.toG R₁) (gb₂ : GBase D.toG R₂) (hρ : gb₂.ρ = τ gb₁.ρ)
    (ht : ∀ i, gb₂.t i = τ.comp (gb₁.t i)) (N N' : ℕ) (M : GenModel gb₁ N) (M' : GenModel gb₁ N') (P : GenModel gb₂ N)
    (P' : GenModel gb₂ N') (f : P.X ⟶ M.X) (f' : P'.X ⟶ M'.X), IsPullback f P.s M.s (spMap τ) →
    IsPullback f' P'.s M'.s (spMap τ) → ∀ (m : GObjMap (down hρ ht rfl P.univ) M.univ f)
    (m' : GObjMap (down hρ ht rfl P'.univ) M'.univ f') (h : G.GAf) (π : M'.X ⟶ M.X) (o : GObj gb₁ N M'.s)
    (ψ : M'.univ.A ⟶ o.A) (φ : GObjMap o M.univ π), π ≫ M.s = M'.s → IsTrans L h M'.univ o ψ →
    ∃ (π₁ : P'.X ⟶ P.X) (o₁ : GObj gb₂ N P'.s) (ψ₁ : P'.univ.A ⟶ o₁.A) (φ₁ : GObjMap o₁ P.univ π₁),
      π₁ ≫ P.s = P'.s ∧ IsTrans L h P'.univ o₁ ψ₁ ∧ π₁ ≫ f = f' ≫ π ∧
        (ψ₁.left ≫ φ₁.φ) ≫ m.φ = m'.φ ≫ ψ.left ≫ φ.φ

def PowComp : Prop :=
  ∀ (S₁ S₂ S₃ : Scheme.{0}) (A₁ : Over S₁) (A₂ : Over S₂) (A₃ : Over S₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) (e : S₁ ⟶ S₃)
    (φ : A₁.left ⟶ A₂.left) (χ : A₂.left ⟶ A₃.left) (ω : A₁.left ⟶ A₃.left) (h₁ : φ ≫ A₂.hom = A₁.hom ≫ f)
    (h₂ : χ ≫ A₃.hom = A₂.hom ≫ g) (h₃ : ω ≫ A₃.hom = A₁.hom ≫ e), f ≫ g = e → φ ≫ χ = ω → ∀ k : ℕ,
    GlobalTheory.KS.powMap f φ h₁ k ≫ GlobalTheory.KS.powMap g χ h₂ k = GlobalTheory.KS.powMap e ω h₃ k

def KNNormal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (M : ℕ),
    (∀ k ∈ L.KN 1, ∀ u ∈ L.KN M, k * u * k⁻¹ ∈ L.KN M) ∧ (0 < M → (L.KN M).relIndex (L.KN 1) ≠ 0)

def cntFn {Γ : Type} [Group Γ] (K K' M : Subgroup Γ) (h y : Γ) : ℂ :=
  (Nat.card {k : K' ⧸ M.subgroupOf K' // h * (k.out : Γ) * y ∈ K} : ℕ)

def CntFn : Prop :=
  ∀ (Γ : Type) [Group Γ] (K K' M : Subgroup Γ) (h : Γ), K ≤ K' → (∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) →
    M.relIndex K' ≠ 0 → (∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) →
    (∀ k ∈ K, ∀ y, cntFn K K' M h (k * y) = cntFn K K' M h y ∧ cntFn K K' M h (y * k) = cntFn K K' M h y) ∧
    (∀ y, cntFn K K' M h y ≠ 0 → ∃ k ∈ K, ∃ c ∈ K', y⁻¹ = k * (h * c)) ∧
    {y : Γ ⧸ K | cntFn K K' M h y.out ≠ 0}.Finite

def CntSum : Prop :=
  ∀ (Γ : Type) [Group Γ] (K K' M : Subgroup Γ) (h : Γ), M ≤ K → K ≤ K' → (∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) →
    (∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) →
    ∀ [Fintype (K' ⧸ K.subgroupOf K')] (Δ : Type) [Fintype Δ] (r : Δ → Γ), (∀ x, r x ∈ K) →
    (∀ k ∈ K, ∃! x, k * (r x)⁻¹ ∈ M) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (P : Γ → V),
    (∀ k ∈ K, ∀ c ∈ K', P (k * (h * c)) = P (h * c)) →
      ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * (z.1.out : Γ) * r z.2) = ∑ᶠ y : Γ ⧸ K, cntFn K K' M h y.out • P y.out⁻¹

def SigmaFEt : Prop :=
  ∀ (Y Z : Scheme.{0}) (s : Y ⟶ Z) [IsFinite s] [Etale s] (I : Type) [Finite I],
    IsFinite (Sigma.desc fun _ : I => s) ∧ Etale (Sigma.desc fun _ : I => s)

def SigmaSplit : Prop :=
  ∀ (Y Z W : Scheme.{0}) (s : Y ⟶ Z) [IsFinite s] [Etale s] (I : Type) [Finite I] (c : W ⟶ Z) (Δ : Type) [Finite Δ]
    (σ : Δ → (W ⟶ Y)), Splits s c σ →
    Splits (Sigma.desc fun _ : I => s) c fun z : I × Δ => σ z.2 ≫ Sigma.ι (fun _ : I => Y) z.1

end UpperTheory.Gal.LocalSmoothExtension
end
end

