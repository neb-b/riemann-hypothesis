module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinSchreierCocycleRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiGPairingEqChGPairingStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_psiG_mul_star_eq_chG : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, psiG S n x * star (Y x) = ∑ᶠ x, chG S n x * star (Y x) := by
  first | (exact @GlobalTheory.psiG_pairing_eq_chG_pairing) | (exact GlobalTheory.psiG_pairing_eq_chG_pairing) | (intros; apply GlobalTheory.psiG_pairing_eq_chG_pairing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiSumEqCharSumAgainstCuspForm
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_sum_eq_char_sum_against_cusp_form : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (S : F[X] → ℂ) (n k : ℕ), S 1 = 0 → ∑ᶠ x, psiG S n x * star (cusp θ n k x) = ∑ᶠ x, chG S n x * star (cusp θ n k x) := by
  first | (exact @GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq) | (exact GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq) | (intros; apply GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Pull1RestrictSurjectiveOfComma
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh

theorem pull1_restrict_surjective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a) → Function.Surjective (CoefMap.restrict F G).pull1 := by
  intro R _ C _ C' _ F G hsep hglue hvan c
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
  have hb : ∀ T : C, ∃ b : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), b t' (u ≫ G.map a) - mp F (G.map a) (b t u) = y.1 t t' a := fun T ↦
    hvan T (fun t t' _ a ↦ y.1 t t' a) fun t t' t'' _ a a' ↦ Z1.comp y a a'
  choose b hb using hb
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t u, mp F u x = b T t (φ ≫ u) - b T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := hb T t t' (φ ≫ u) a
    have k2 := hb T' t t' u a
    rw [Category.assoc] at k1
    rw [map_sub]
    linear_combination k1 - k2
  choose x hx using hx
  have hxc : x ∈ Z1 F := fun T T' T'' φ ψ ↦ sub_eq_zero.1 (hsep T'' _ fun t u ↦ by
    have k1 := hx T T'' (φ ≫ ψ) t u
    have k2 := hx T T' φ t (ψ ≫ u)
    have k3 := hx T' T'' ψ t u
    rw [mp_comp] at k2
    simp only [map_sub, map_add (f := _), Category.assoc] at k1 k2 ⊢
    linear_combination k1 - k2 - k3)
  refine ⟨H1.mk F ⟨x, hxc⟩, ?_⟩
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
  refine ⟨fun t ↦ -b (G.obj t) t (𝟙 _), ?_⟩
  funext t t' a
  have k1 := hx _ _ (G.map a) t' (𝟙 _)
  have k2 := hb (G.obj t) t t' (𝟙 _) a
  rw [mp_id, Category.comp_id] at k1
  rw [Category.id_comp] at k2
  show -b _ t' (𝟙 _) - mp F (G.map a) (-b _ t (𝟙 _)) = x _ _ (G.map a) - (show F.obj (G.obj t') from y.1 t t' a)
  rw [map_neg]
  linear_combination -k1 - k2

end GlobalTheory.CatCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullHyp1RestrictInjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp1_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h1 : Function.Injective (CoefMap.restrict F G).pull1)
    (h0 : ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) →
      ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t)
    (hf : Function.Injective (pullGlob1 (CoefMap.restrict F G))) :
    Function.Injective (pullHyp1 (CoefMap.restrict F G)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, rfl⟩ := Hyp1.mk_surjective F c
  have ht : toO F (Hyp1.mk F x) = 0 := h1 (by rw [← toO_pullHyp1, hc, map_zero, map_zero])
  rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
  obtain ⟨g, hg'⟩ := hc
  obtain ⟨g', rfl⟩ : ∃ g' : ∀ t, F.obj (G.obj t), (g' : Tot0 (G ⋙ F)) = g := ⟨g, rfl⟩
  have hf' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' - mp F (G.map a) (g' t) = x.1.1 _ _ (G.map a) :=
    fun t t' a ↦ congrArg (fun y : Tot1 (G ⋙ F) ↦ y.1 t t' a) hg'
  have hω : ∀ t, D R _ (g' t) = x.1.2 (G.obj t) := fun t ↦
    (congrArg (fun y : Tot1 (G ⋙ F) ↦ y.2 t) hg').trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _)
  rw [toO_mk, H1.mk_eq_zero] at ht
  obtain ⟨g₀, hg₀⟩ := ht
  have hg0 : ∀ (T T' : C) (φ : T ⟶ T'), g₀ T' - mp F φ (g₀ T) = x.1.1 T T' φ := fun T T' φ ↦
    congrFun (congrFun (congrFun hg₀ T) T') φ
  obtain ⟨h, hh, hhG⟩ := h0 (fun t ↦ g' t - g₀ (G.obj t)) (fun t t' a ↦ by
    have e1 := hf' a
    have e2 := hg0 _ _ (G.map a)
    rw [map_sub]
    linear_combination e1 - e2)
  let θ : Glob1 F := ⟨fun T ↦ x.1.2 T - D R _ (g₀ T), fun T T' φ ↦ by
    show x.1.2 T' - D R _ (g₀ T') = p1 F φ (x.1.2 T - D R _ (g₀ T))
    rw [map_sub, p1_D, cechDeRhamTotalCocyclesOne.conn x φ, ← hg0 T T' φ, map_sub]; abel⟩
  let ψ : Glob1 F := ⟨fun T ↦ D R _ (h T), fun T T' φ ↦ by
    show D R _ (h T') = p1 F φ (D R _ (h T))
    rw [p1_D, ← hh φ]⟩
  have hθψ : θ = ψ := hf (Subtype.ext (funext fun t ↦ by
    change q1 (CoefMap.restrict F G) t (θ.1 (G.obj t)) = q1 (CoefMap.restrict F G) t (ψ.1 (G.obj t))
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, cechDeRhamCoefMapOneForms_restrictAlongFunctor]
    show x.1.2 (G.obj t) - D R _ (g₀ (G.obj t)) = D R _ (h (G.obj t))
    rw [hhG, map_sub, hω]))
  refine Hyp1.mk_eq_zero.2 ⟨g₀ + h, Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · rw [dTot0_f]
    simp only [Pi.add_apply, map_add (f := _)]
    linear_combination hh φ + hg0 T T' φ
  · have e : x.1.2 T - D R _ (g₀ T) = D R _ (h T) := congrArg (fun ω : Glob1 F ↦ ω.1 T) hθψ
    rw [dTot0_ω, Pi.add_apply, map_add (f := _), ← e]
    abel

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullHyp1RestrictSurjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp1_restrict_surjective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hO : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
        κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
      ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (η : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u η = 0) → η = 0) :
    Function.Surjective (pullHyp1 (CoefMap.restrict F G)) := by
  intro c'
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (toO _ (Hyp1.mk _ c'))
  obtain ⟨f, rfl⟩ := H1.mk_surjective F h0
  rw [toO_mk, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hh
  obtain ⟨g', hg'⟩ := hh
  let g : ∀ t, F.obj (G.obj t) := g'
  let f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := c'.1.1
  let ω' : ∀ t, Ω[F.obj (G.obj t)⁄R] := c'.1.2
  have hga : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) - f' t t' a := fun t t' a ↦
    congrFun (congrFun (congrFun hg' t) t') a
  have hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      D R _ (f.1 T T'' (φ ≫ ψ)) = p1 F ψ (D R _ (f.1 T T' φ)) + D R _ (f.1 T' T'' ψ) := by
    intro T T' T'' φ ψ
    rw [Z1.comp f φ ψ, map_add (f := _), p1_D]
  let θ' : ∀ t, Ω[F.obj (G.obj t)⁄R] := fun t ↦ ω' t + D R _ (g t)
  have hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      D R _ (f.1 _ _ (G.map a)) = θ' t' - p1 F (G.map a) (θ' t) := by
    intro t t' a
    have e1 : ω' t' = p1 F (G.map a) (ω' t) + D R _ (f' t t' a) := cechDeRhamTotalCocyclesOne.conn c' a
    have e2 : f.1 _ _ (G.map a) = g t' - mp F (G.map a) (g t) + f' t t' a :=
      (sub_eq_iff_eq_add.1 (hga a).symm)
    simp only [θ']
    rw [e1, e2]
    simp only [map_add (f := _), map_sub, p1_D]
    abel
  obtain ⟨θ, hθ⟩ := hc (fun T T' φ ↦ D R _ (f.1 T T' φ)) hκ θ' hθ'
  have hθ2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), D R _ (f.1 T T' φ) = θ T' - p1 F φ (θ T) := hθ
  let ψ0 : Glob1 (G ⋙ F) := ⟨fun t ↦ θ' t - θ (G.obj t), fun t t' a ↦ by
    change θ' t' - θ (G.obj t') = p1 F (G.map a) (θ' t - θ (G.obj t))
    have e := (hθ2 (G.map a)).symm.trans (hθ' a)
    rw [map_sub]
    rw [← sub_eq_zero] at e ⊢
    rw [← neg_eq_zero, ← e]
    abel⟩
  obtain ⟨ψ, hψ⟩ := hf ψ0
  have hψG : ∀ t, ψ.1 (G.obj t) = θ' t - θ (G.obj t) := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun z : Glob1 (G ⋙ F) ↦ z.1 t) hψ)
  let ω : A0 F := fun T ↦ θ T + ψ.1 T
  have hωG : ∀ t, ω (G.obj t) = θ' t := fun t ↦ by
    change θ (G.obj t) + ψ.1 (G.obj t) = _
    rw [hψG]; abel
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R _ (f.1 T T' φ) := by
    intro T T' φ
    change θ T' + ψ.1 T' = p1 F φ (θ T + ψ.1 T) + D R _ (f.1 T T' φ)
    rw [map_add (f := _), ← ψ.2 φ, hθ2 φ]; abel
  have hclosed : ∀ T, dOne R _ (ω T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : p1 F u (ω T) = ω' t + D R _ (g t) - D R _ (f.1 _ _ u) := by
      rw [eq_sub_iff_add_eq, ← hconn u, hωG]
    rw [pOm_dOne, e, map_sub, map_add (f := _), dOne_D, dOne_D]
    have e3 : dOne R _ (ω' t) = 0 := cechDeRhamTotalCocyclesOne.closed c' t
    rw [e3]; simp
  let c : cechDeRhamTotalCocyclesOne F := ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hconn, hclosed⟩⟩
  refine ⟨Hyp1.mk F c, ?_⟩
  rw [pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨g', Tot1.ext (fun t t' a ↦ hga a) fun t ↦ ?_⟩
  have e4 : q1 (CoefMap.restrict F G) t (ω (G.obj t)) = θ' t := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).trans (hωG t)
  change D R _ (g t) = q1 (CoefMap.restrict F G) t (ω (G.obj t)) - c'.1.2 t
  rw [e4]
  change _ = ω' t + D R _ (g t) - ω' t
  abel

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProjBundleFormulaMapOfFactor
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PbfNatl

theorem pull_htCast' (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem pull_cpow' (q : ℕ) [NeZero q] (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x : Ht q E 2 1) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_htCast', (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_htCast', (hA q).1, ih]

theorem pull_pbfMap_of_factor : DivisorNaturality → ∀ (q : ℕ) [NeZero q] {E B P : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))
    (L : B ⟶ ofCat (glCat 1)) (θ : P ⟶ pullback V (PGL.pr N)) (f : P ⟶ E) (g : P ⟶ B), Inv q B →
    Inv q (pullback V (PGL.pr N)) → θ ≫ pullback.fst _ _ = f → θ ≫ pullback.snd _ _ ≫ PGL.line N = g ≫ L →
    ∀ (n i : ℤ) (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))),
    pull _ θ _ _ (pbfMap q V n i a) = ∑ j : Fin N, ((cup q (pull _ f _ _ (a j)) (pull _ g _ _ (cpow q (c1 q L) j))).cast (by ring) (by ring) : Ht q P n i) := by
  intro hA q _ E B P N V L θ f g hB hP hf hg n i a
  unfold pbfMap
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_htCast', (hA q).1, ← pull_comp, hf, pull_cpow' q hA _ hP, (hA q).2.2.1 _ _ hP,
    pull_cpow' q hA _ hB, (hA q).2.2.1 _ _ hB, hg]

end GlobalTheory.EtC.PbfNatl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_hypercohomology_bijective' : A1 := by
  intro R _ K L f _ F n
  haveI : (res R F).IsKInjective := (_root_.GlobalTheory.EtC.ResBasic.res_basic R F).1
  exact GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R f (res R F) n

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionToSiegelDomain
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ArtCoh

theorem ht_subsingleton_of_ringEquiv (q : ℕ) {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (n i : ℤ)
    [h : Subsingleton (Ht q (sp R) n i)] : Subsingleton (Ht q (sp S) n i) := by
  have hid : spMap (e : R →+* S) ≫ spMap (e.symm : S →+* R) = 𝟙 (sp S) := by
    rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by ext x; simp
    rw [this]
    simp
  constructor
  intro x y
  have hx : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ x) = x := by
    rw [← pull_comp, hid, pull_id]
  have hy : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ y) = y := by
    rw [← pull_comp, hid, pull_id]
  rw [← hx, ← hy, Subsingleton.elim (pull _ (spMap (e.symm : S →+* R)) _ _ x)
    (pull _ (spMap (e.symm : S →+* R)) _ _ y)]

theorem ht_subsingleton_prod (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ)
    [Subsingleton (Ht q (sp A) n i)] [Subsingleton (Ht q (sp B) n i)] : Subsingleton (Ht q (sp (A × B)) n i) := by
  constructor
  intro x y
  exact (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A B n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := by ext x; exact Subsingleton.elim _ _
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q Z Z n i).2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  rw [← h1, ← h2]

theorem ht_subsingleton_pi (q : ℕ) (n i : ℤ) (ι : Type) [Finite ι] : ∀ (R : ι → Type) [∀ j, CommRing (R j)],
    (∀ j, Subsingleton (Ht q (sp (R j)) n i)) → Subsingleton (Ht q (sp (∀ j, R j)) n i) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro R _ hR
    have := ih (fun a => R (e a)) (fun a => hR (e a))
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piCongrLeft R e) n i
  | h_empty =>
    intro R _ _
    exact ht_subsingleton_of_subsingleton q _ n i
  | h_option ih =>
    intro R _ hR
    have h1 := hR none
    have h2 := ih (fun a => R (some a)) (fun a => hR (some a))
    have := ht_subsingleton_prod q (R none) (∀ a, R (some a)) n i
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piOptionEquivProd (R := R)).symm n i

theorem ht_subsingleton_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ),
    (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  intro q K _ _ _ n i h
  have := ht_subsingleton_pi q n i (MaximalSpectrum K) (fun M => K ⧸ M.asIdeal) h
  exact ht_subsingleton_of_ringEquiv q (IsArtinianRing.equivPi K).toRingEquiv.symm n i

end GlobalTheory.EtC.ArtCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictGlob1Bijective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem restrict_glob1_bijective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → Function.Bijective (pullGlob1 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hsep hglue
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    apply Subtype.ext
    funext T
    refine hsep T (ω.1 T) fun t u ↦ ?_
    have h1 := congrArg (fun x : Glob1 (G ⋙ F) ↦ x.1 t) hω
    have h2 : (pullGlob1 (CoefMap.restrict F G) ω).1 t = ω.1 (G.obj t) := cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _
    rw [← ω.2 u, ← h2, h1]
    rfl
  · intro ω'
    have hc : ∀ (T : C), ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t), p1 F u ω = ω'.1 t :=
      fun T ↦ hglue T (fun t _ ↦ ω'.1 t) fun t t' u a ↦ ω'.2 a
    choose ω hω using hc
    have hglob : ω ∈ Glob1 F := by
      intro T T' φ
      rw [← sub_eq_zero]
      refine hsep T' _ fun t u ↦ ?_
      rw [map_sub, ← oneFormsMapOfFunctorMorphism_comp, hω, hω, sub_self]
    refine ⟨⟨ω, hglob⟩, Subtype.ext (funext fun t ↦ ?_)⟩
    change q1 (CoefMap.restrict F G) t (ω (G.obj t)) = ω'.1 t
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, ← hω (G.obj t) t (𝟙 _), oneFormsMapOfFunctorMorphism_id]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPull1InjectiveOfSepGlue
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.CoefMap

theorem restrict_pull1_injective_of_sep_glue {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hsep : ∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0)
    (hglue : ∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)),
      (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) →
      ∃ x : F.obj T, ∀ t u, mp F u x = s t u) :
    Function.Injective (CoefMap.restrict F G).pull1 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
  obtain ⟨g₀, hg⟩ := hc
  let g : ∀ t, F.obj (G.obj t) := fun t ↦ g₀ t
  have hg' : ∀ t t' (a : t ⟶ t'), g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) := fun t t' a ↦
    congrFun (congrFun (congrFun hg t) t') a
  have h1 : ∀ T : C, ∃ x : F.obj T, ∀ t (u : T ⟶ G.obj t), mp F u x = g t - f.1 T _ u := by
    intro T
    refine hglue T (fun t u ↦ g t - f.1 T _ u) fun t t' u a ↦ ?_
    have k1 := Z1.comp f u (G.map a)
    have k2 := hg' t t' a
    simp only [map_sub]
    linear_combination k2 - k1
  choose x hx using h1
  refine H1.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply]
  refine (sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)).symm
  have k1 := Z1.comp f φ u
  have k2 := hx T' t u
  have k3 := hx T t (φ ≫ u)
  rw [mp_comp] at k3
  simp only [map_sub]
  linear_combination k3 - k2 - k1

end GlobalTheory.CatCoh.CoefMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityEtaleLocallyPowPrimitiveRootStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootOfUnity_etaleLocally_pow_primitiveRoot : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ ω : (Γ(U, ⊤))ˣ, ω ^ q = 1 →
    Loc U fun V g => ∃ (ζ : Prim q Γ(V, ⊤)) (a : ℕ), (Units.map g.appTop.hom.toMonoidHom ω : Γ(V, ⊤)) = ζ.1 ^ a := by
  first | (exact @GlobalTheory.EtC.RootLoc.root_loc_pow_prim) | (exact GlobalTheory.EtC.RootLoc.root_loc_pow_prim) | (intros; apply GlobalTheory.EtC.RootLoc.root_loc_pow_prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFixedNearOneSiegelParabolicStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_fixed_near_one_siegelParabolic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  first | exact @GlobalTheory.KSp.parFun_fixed_near_one | exact GlobalTheory.KSp.parFun_fixed_near_one | (intros; apply GlobalTheory.KSp.parFun_fixed_near_one <;> assumption)
end

