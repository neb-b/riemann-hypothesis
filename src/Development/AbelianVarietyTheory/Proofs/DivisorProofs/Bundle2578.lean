module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperThetaSetup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLift

theorem transport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀)
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧
    (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧
    (∀ x₂ x₂' E, x₂'.left ≫ u₂.φ = x₂.left ≫ u₂.φ ≫ (ε₂ E).left → (T x₂').left ≫ u.φ = (T x₂).left ≫ u.φ ≫ (ε' E).left) ∧
    (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ c y h c₀ hc R' fg frac hth' hev ρ' ε' hS hi hR y₀ hy₀ u c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS₂ hi₂ hR₂ y₂ hy₂
  obtain ⟨V₂, _, _, _, _, hV₂c, hV₂n, σ, hσ, hval⟩ := _root_.GlobalTheory.Poinc.exists_complete_dvr_values g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h u.V u.complete u.norm_le
  obtain ⟨u', τ, e, T, hτ, hpsi, hT, hfw, hbw⟩ := GlobalTheory.T.uniformisedModel_baseChange_complete_dvr_extension _ _ _ ρ' p y₀ u V₂ hV₂c hV₂n σ hσ
  have hval' : ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))),
      D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing u'.V) (PadicAlgCl p)).range := by
    intro a ha
    obtain ⟨b, hb⟩ := hval a ha
    exact ⟨τ b, by rw [← hb, ← hτ]; rfl⟩
  have hSS := _root_.GlobalTheory.Poinc.same_chain_deep g n F W Z i X₁ ε₁ D c₀ hc R' fg frac hth' hev ρ' ε' c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS hS₂
  obtain ⟨f₂, φ₂, hf₂, hcart, hlb, htor, heps⟩ := _root_.GlobalTheory.Poinc.special_transport g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h
    c₀ hc R' fg frac hth' hev ρ' ε' hR y₀ hy₀ c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hSS hR₂ y₂ hy₂
    (FractionRing u'.V) (algebraMap _ _) u'.yK u'.fac hval' u'.A u'.φ u'.cart u'.lb
  let u₂ : ρ₂.UTest p y₂ :=
    { V := u'.V, complete := u'.complete, norm_le := u'.norm_le, yK := f₂, fac := hf₂, A := u'.A, φ := φ₂,
      cart := hcart, lb := hlb, G := u'.G, semi := u'.semi, D := u'.D, U := u'.U }
  refine ⟨u₂, e, T, hpsi, ?_, ?_, hfw, hbw⟩
  · intro x₂ a
    rw [hT]
    exact htor x₂.left a (Over.w x₂)
  · intro x₂ x₂' E hxx
    rw [hT, ← Category.assoc, hT, Category.assoc]
    exact (heps x₂.left x₂'.left E (Over.w x₂) (Over.w x₂')).1 hxx

end GlobalTheory.Poinc.GLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingsCommonGeometricFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.USpreadU

open GlobalTheory.Poinc.GalTrans GlobalTheory.CechPic

theorem exists_model {O Ω R' R'' : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R'] [CommRing R'']
    (f' : R' →+* O) (f'' : R'' →+* O) (P' : PolAV (Sp R')) (P'' : PolAV (Sp R'')) (Q : PolAV (Sp Ω))
    {b' : Q.A.left ⟶ P'.A.left} {b'' : Q.A.left ⟶ P''.A.left}
    (hb' : IsGrpPullback Q.A P'.A (spMap ((algebraMap O Ω).comp f')) b')
    (hb'' : IsGrpPullback Q.A P''.A (spMap ((algebraMap O Ω).comp f'')) b'')
    (l' : LBIso Q.L (P'.L.pull b')) (l'' : LBIso Q.L (P''.L.pull b'')) :
    ∃ (B : PolAV (Sp O)) (c' : B.A.left ⟶ P'.A.left) (c'' : B.A.left ⟶ P''.A.left) (j : Q.A.left ⟶ B.A.left),
      IsGrpPullback B.A P'.A (spMap f') c' ∧ IsGrpPullback B.A P''.A (spMap f'') c'' ∧
      LBIso B.L (P'.L.pull c') ∧ LBIso B.L (P''.L.pull c'') ∧
      IsGrpPullback Q.A B.A (spMap (algebraMap O Ω)) j ∧ j ≫ c' = b' ∧ j ≫ c'' = b'' ∧
      ∀ (t' : Sp R' ⟶ P'.A.left) (t'' : Sp R'' ⟶ P''.A.left) (w : Sp Ω ⟶ Q.A.left), t' ≫ P'.A.hom = 𝟙 _ →
        t'' ≫ P''.A.hom = 𝟙 _ → w ≫ Q.A.hom = 𝟙 _ → w ≫ b' = spMap ((algebraMap O Ω).comp f') ≫ t' →
        w ≫ b'' = spMap ((algebraMap O Ω).comp f'') ≫ t'' →
        ∃ w₀ : Sp O ⟶ B.A.left, w₀ ≫ B.A.hom = 𝟙 _ ∧ w₀ ≫ c' = spMap f' ≫ t' ∧ w₀ ≫ c'' = spMap f'' ≫ t'' := by
  obtain ⟨B, c', -, hc', lc'⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f') P'
  obtain ⟨B₂, c₂, -, hc₂, lc₂⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f'') P''
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P' B Q (sp_comp rfl) hc' hb' lc' l'
  obtain ⟨j₂, hj₂, lj₂, ej₂⟩ := exists_factor P'' B₂ Q (sp_comp rfl) hc₂ hb'' lc₂ l''
  obtain ⟨E, hE, lE, eE⟩ := exists_iso B B₂ Q hj hj₂ lj lj₂
  have hc'' : IsGrpPullback B.A P''.A (spMap f'') (E ≫ c₂) := (hE.comp hc₂).congr (Category.id_comp _) rfl
  have lc'' := lb_comp B.isLB B₂.isLB P''.isLB lE lc₂
  have ej'' : j ≫ E ≫ c₂ = b'' := by rw [← Category.assoc, eE, ej₂]
  generalize E ≫ c₂ = c'' at hc'' lc'' ej''
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap O Ω)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap O Ω)) :=
    ExtUnique.spec_fractionRing O Ω
  have := P''.isAb.proper
  refine ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej, ej'', fun t' t'' w ht' ht'' hw e' e'' => ?_⟩
  have w₁ : (spMap f' ≫ t') ≫ P'.A.hom = 𝟙 _ ≫ spMap f' := by rw [Category.assoc, ht']; simp
  have k₁ := hc'.1.lift_fst _ _ w₁
  have k₂ := hc'.1.lift_snd _ _ w₁
  generalize hc'.1.lift _ _ w₁ = t at k₁ k₂
  have a₁ : spMap (algebraMap O Ω) ≫ t = w ≫ j := hc'.1.hom_ext
    (by rw [Category.assoc, k₁, Category.assoc, ej, e', ← Category.assoc, sp_comp rfl])
    (by rw [Category.assoc, k₂, Category.assoc, hj.1.w, reassoc_of% hw, Category.comp_id])
  have a₂ : t ≫ c'' = spMap f'' ≫ t'' := ExtUnique.hom_ext_of_dominant P''.A.hom
    (by rw [Category.assoc, hc''.1.w, reassoc_of% k₂, Category.assoc, ht'', Category.comp_id])
    (spMap (algebraMap O Ω))
    (by rw [reassoc_of% a₁, ej'', e'', ← Category.assoc, sp_comp rfl])
  exact ⟨t, k₂, k₁, a₂⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (σ : X.Ω₁ →+* X.Ω₁) (s : X.M.Z ⟶ X.M.Z), X.M.pt ≫ s = spMap σ ≫ X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X.M.Z) (S' S'' : ThetaSys X.o₁ X.Ω₁) (ρ' : S'.Real) (ρ'' : S''.Real), S'.R ≤ X.M.O (y (closedPoint (PadicAlgCl p))) → S''.R ≤ X.M.O ((y ≫ s) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S'.R →+* PadicAlgCl p) (y₁ : S''.R →+* PadicAlgCl p), (∀ a : S'.R, y₀ a = X.M.val y a) → (∀ a : S''.R, y₁ a = X.M.val (y ≫ s) a) → ∀ (u : ρ'.UTest p y₀) (u₁ : ρ''.UTest p y₁) (u' : Sp (ratHull S'.R) ⟶ Xo.XF cf) (u'' : Sp (ratHull S''.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S'.R))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (G'' : Over (Sp (ratHull S''.R))) (_ : GrpObj G'') (α'' : G''.left ⟶ ρ''.P.A.left) (β'' : G''.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat S'.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → IsGrpPullback G'' ρ''.P.A (spMap (toRat S''.R)) α'' → IsGrpPullback G'' Xo.univ.t.G (u'' ≫ pullback.fst _ _) β'' → LBIso (ρ''.P.L.pull α'') (Xo.univ.t.PP.L.pull β'') → ∀ (W₀ : Over (Sp X.Ω₁)) (_ : GrpObj W₀) (k₀ : W₀.left ⟶ G.left) (k₀'' : W₀.left ⟶ G''.left), IsGrpPullback W₀ G (spMap (ratHull S'.R).val.toRingHom) k₀ → IsGrpPullback W₀ G'' (spMap (σ.comp (ratHull S''.R).val.toRingHom)) k₀'' → k₀ ≫ β = k₀'' ≫ β'' → ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u₁.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u₁.A.A (spMap (algebraMap (FractionRing u₁.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u₁.A.L.pull a') ∧ (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp X.Ω₁ ⟶ W₀.left), w ≫ W₀.hom = 𝟙 _ → w ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left → w ≫ k₀'' ≫ α'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left → ∃ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u₁.V) (PadicAlgCl p) ⟶ u₁.A.A), v ≫ P₀.A.hom = 𝟙 _ ∧ v ≫ a = x.left ∧ v ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u₁.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧ ∀ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (g : Sp (PadicAlgCl p) ⟶ G.left) (h : Sp (PadicAlgCl p) ⟶ G''.left), v ≫ P₀.A.hom = 𝟙 _ → g ≫ α = v ≫ a ≫ u.φ → h ≫ α'' = v ≫ a' ≫ u₁.φ → g ≫ β = h ≫ β'' := by
  intro E _ _ _ H Dw l Xo cf C X σ s hs p _ y S' S'' ρ' ρ'' h' h'' y₀ y₁ hy₀ hy₁ u u₁ u' u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ k₀'' hk₀ hk₀'' hkb
  haveI := X.ar.char
  set z := y (closedPoint (PadicAlgCl p)) with hz
  have hyz : Set.range y = {z} := RatModel.range_eq_singleton y _
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z) := X.M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z) := X.normal.isIntegrallyClosed_stalk z
  haveI : IsIntegrallyClosed (X.M.O z) := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z)

  have hU : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X.M.O z) := fun n hn => by
    rw [← RatModel.val_ne_zero_iff hyz]
    have e := map_intCast (RatModel.valHom y z hyz) n
    rw [RatModel.valHom_apply] at e
    rw [e]
    exact Int.cast_ne_zero.2 hn
  have hmem : ∀ {x : X.Ω₁} (n : ℤ), n ≠ 0 → (n : X.Ω₁) * x ∈ X.M.O z → x ∈ X.M.O z := fun {x} n hn h => by
    obtain ⟨w, hw⟩ := hU n hn
    have e1 : (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * (n : X.Ω₁) = 1 := by
      have := congrArg (fun t : X.M.O z => (t : X.Ω₁)) w.inv_mul
      simpa [hw] using this
    have : x = (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * ((n : X.Ω₁) * x) := by rw [← mul_assoc, e1, one_mul]
    rw [this]; exact mul_mem (SetLike.coe_mem _) h
  have hR' : ratHull S'.R ≤ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    exact hmem n hn (h' h)
  have hR'' : ∀ x ∈ ratHull S''.R, σ x ∈ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    refine hmem n hn ?_
    have := map_mem_O hs (h'' h)
    rwa [map_mul, map_intCast] at this
  let f'Q : ratHull S'.R →+* X.M.O z := (Subalgebra.inclusion hR').toRingHom
  let f''Q : ratHull S''.R →+* X.M.O z := (σ.comp (ratHull S''.R).val.toRingHom).codRestrict (X.M.O z) fun x => hR'' x x.2
  let f' : S'.R →+* X.M.O z := f'Q.comp (toRat S'.R)
  let f'' : S''.R →+* X.M.O z := f''Q.comp (toRat S''.R)

  obtain ⟨Q, c, hc, lc⟩ := exists_pol_baseChange ρ'.P (spMap S'.R.val.toRingHom)
  have hW : IsGrpPullback W₀ ρ'.P.A (spMap S'.R.val.toRingHom) (k₀ ≫ α) :=
    (hk₀.comp hα).congr (spMap_val_toRat S'.R) rfl
  have ec : hW.1.lift c Q.A.hom hc.1.w ≫ k₀ ≫ α = c := hW.1.lift_fst _ _ _
  have ew : hW.1.lift c Q.A.hom hc.1.w ≫ W₀.hom = Q.A.hom := hW.1.lift_snd _ _ _
  generalize hW.1.lift c Q.A.hom hc.1.w = e at ec ew
  have he : IsGrpPullback Q.A W₀ (𝟙 _) e :=
    hW.cancel (hc.congr (Category.id_comp _).symm ec.symm) (by rw [ew, Category.comp_id])
  have hb'' : IsGrpPullback Q.A ρ''.P.A (spMap (σ.comp S''.R.val.toRingHom)) (e ≫ k₀'' ≫ α'') :=
    (he.comp (hk₀''.comp hα'')).congr (by rw [Category.id_comp]; exact sp_comp (RingHom.ext fun _ => rfl)) rfl
  have iso_iff {X Y : Scheme.{0}} {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (φ : X ⟶ Y) :
      LBIso L (M.pull φ) ↔ cls L hL = GlobalTheory.CechPic.pull φ (cls M hM) := by
    rw [← cls_pull hM φ (pull_isLB hM φ)]
    exact (cls_eq_iff hL _).symm
  have hA : GlobalTheory.CechPic.pull α (cls ρ'.P.L ρ'.P.isLB) = GlobalTheory.CechPic.pull β (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ'.P.isLB α (pull_isLB ρ'.P.isLB α)]
    exact (iso_iff (pull_isLB ρ'.P.isLB α) Xo.univ.t.PP.isLB β).1 hL
  have hA'' : GlobalTheory.CechPic.pull α'' (cls ρ''.P.L ρ''.P.isLB) = GlobalTheory.CechPic.pull β'' (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ''.P.isLB α'' (pull_isLB ρ''.P.isLB α'')]
    exact (iso_iff (pull_isLB ρ''.P.isLB α'') Xo.univ.t.PP.isLB β'').1 hL''
  have hk : GlobalTheory.CechPic.pull k₀ (GlobalTheory.CechPic.pull β (cls _ Xo.univ.t.PP.isLB)) = GlobalTheory.CechPic.pull k₀'' (GlobalTheory.CechPic.pull β'' (cls _ Xo.univ.t.PP.isLB)) := by
    rw [← pull_comp, ← pull_comp, hkb]
  have lb'' : LBIso Q.L (ρ''.P.L.pull (e ≫ k₀'' ≫ α'')) := by
    rw [iso_iff Q.isLB ρ''.P.isLB, (iso_iff Q.isLB ρ'.P.isLB _).1 lc, ← ec]
    simp only [pull_comp]
    rw [hA, hA'', hk]

  obtain ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej', ej'', ht⟩ :=
    exists_model f' f'' ρ'.P ρ''.P Q (b' := c) (b'' := e ≫ k₀'' ≫ α'') hc hb'' lc lb''

  let v : X.M.O z →+* PadicAlgCl p := RatModel.valHom y z hyz
  have e₀ : v.comp f' = y₀ := RingHom.ext fun x => (hy₀ x).symm
  have e₁ : v.comp f'' = y₁ := RingHom.ext fun x => ((hy₁ x).trans (val_comp hs y _ (h'' x.2))).symm
  obtain ⟨P₀, d, hd, ld⟩ := exists_pol_baseChange B (spMap v)
  have hd' : IsGrpPullback P₀.A ρ'.P.A (spMap y₀) (d ≫ c') := (hd.comp hc').congr (sp_comp e₀) rfl
  have hd'' : IsGrpPullback P₀.A ρ''.P.A (spMap y₁) (d ≫ c'') := (hd.comp hc'').congr (sp_comp e₁) rfl
  obtain ⟨a, ha, la, ea, xa⟩ := exists_to_test u P₀ hd' (lb_comp P₀.isLB B.isLB ρ'.P.isLB ld lc')
  obtain ⟨a', ha', la', ea', xa'⟩ := exists_to_test u₁ P₀ hd'' (lb_comp P₀.isLB B.isLB ρ''.P.isLB ld lc'')
  refine ⟨P₀, a, a', ha, ha', la, la', fun k' k'' w hw c1 c2 => ?_, fun v₁ g h hv₁ hg hh => ?_⟩
  · have ww : w ≫ W₀.hom = 𝟙 _ ≫ 𝟙 _ := by rw [hw]; simp
    have q1 : he.1.lift w (𝟙 _) ww ≫ e = w := he.1.lift_fst _ _ _
    have q2 : he.1.lift w (𝟙 _) ww ≫ Q.A.hom = 𝟙 _ := he.1.lift_snd _ _ _
    generalize he.1.lift w (𝟙 _) ww = wQ at q1 q2
    obtain ⟨w₀, hw₀, g', g''⟩ := ht (ρ'.pt k').left (ρ''.pt k'').left wQ (Over.w (ρ'.pt k')) (Over.w (ρ''.pt k''))
      q2 (by rw [← ec, reassoc_of% q1, c1]; rfl) (by rw [reassoc_of% q1, c2]; rfl)
    have w₂ : (spMap v ≫ w₀) ≫ B.A.hom = 𝟙 _ ≫ spMap v := by rw [Category.assoc, hw₀]; simp
    have r1 : hd.1.lift _ _ w₂ ≫ d = spMap v ≫ w₀ := hd.1.lift_fst _ _ _
    have r2 : hd.1.lift _ _ w₂ ≫ P₀.A.hom = 𝟙 _ := hd.1.lift_snd _ _ _
    generalize hd.1.lift _ _ w₂ = wK at r1 r2
    obtain ⟨x, hx⟩ := xa wK r2
    obtain ⟨x', hx'⟩ := xa' wK r2
    refine ⟨wK, x, x', r2, hx, hx', ?_, ?_⟩
    · rw [← hx, Category.assoc, ea, reassoc_of% r1, g', ← Category.assoc, sp_comp e₀]
    · rw [← hx', Category.assoc, ea', reassoc_of% r1, g'', ← Category.assoc, sp_comp e₁]

  ·
    have wm' : c' ≫ ρ'.P.A.hom = (B.A.hom ≫ spMap f'Q) ≫ spMap (toRat S'.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc'.1.w
    have wm'' : c'' ≫ ρ''.P.A.hom = (B.A.hom ≫ spMap f''Q) ≫ spMap (toRat S''.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc''.1.w
    have m1 : hα.1.lift c' _ wm' ≫ α = c' := hα.1.lift_fst _ _ _
    have m2 : hα.1.lift c' _ wm' ≫ G.hom = B.A.hom ≫ spMap f'Q := hα.1.lift_snd _ _ _
    have m1'' : hα''.1.lift c'' _ wm'' ≫ α'' = c'' := hα''.1.lift_fst _ _ _
    have m2'' : hα''.1.lift c'' _ wm'' ≫ G''.hom = B.A.hom ≫ spMap f''Q := hα''.1.lift_snd _ _ _
    generalize hα.1.lift c' _ wm' = m' at m1 m2
    generalize hα''.1.lift c'' _ wm'' = m'' at m1'' m2''
    have key : m' ≫ β = m'' ≫ β'' := by
      haveI := Xo.univ.proper
      haveI : IsSeparated Xo.s := GlobalTheory.LevelQuotRep.isSeparated_of_qproj Xo.qproj
      obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap (X.M.O z) X.Ω₁)) ∧
          IsSchemeTheoreticallyDominant (spMap (algebraMap (X.M.O z) X.Ω₁)) :=
        ExtUnique.spec_fractionRing (X.M.O z) X.Ω₁
      haveI := B.isAb.smooth
      haveI : IsSchemeTheoreticallyDominant j := .of_isPullback hj.1.flip
      refine ExtUnique.hom_ext_of_dominant (Xo.univ.t.G.hom ≫ Xo.s ≫ terminal.from _) (terminal.hom_ext _ _) j ?_
      have n1a : (j ≫ m') ≫ α = (e ≫ k₀) ≫ α := by rw [Category.assoc, m1, ej', Category.assoc, ec]
      have n1b : (j ≫ m') ≫ G.hom = (e ≫ k₀) ≫ G.hom := by
        rw [Category.assoc, m2, reassoc_of% hj.1.w, Category.assoc, hk₀.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n1 : j ≫ m' = e ≫ k₀ := hα.1.hom_ext n1a n1b
      have n2a : (j ≫ m'') ≫ α'' = (e ≫ k₀'') ≫ α'' := by rw [Category.assoc, m1'', ej'', Category.assoc]
      have n2b : (j ≫ m'') ≫ G''.hom = (e ≫ k₀'') ≫ G''.hom := by
        rw [Category.assoc, m2'', reassoc_of% hj.1.w, Category.assoc, hk₀''.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n2 : j ≫ m'' = e ≫ k₀'' := hα''.1.hom_ext n2a n2b
      rw [reassoc_of% n1, reassoc_of% n2, hkb]
    have hg' : g ≫ α = v₁ ≫ d ≫ c' := by rw [hg, ea]
    have hh' : h ≫ α'' = v₁ ≫ d ≫ c'' := by rw [hh, ea']
    have g1 : g = v₁ ≫ d ≫ m' := hα.1.hom_ext (by rw [hg', Category.assoc, Category.assoc, m1])
      ((existsUnique_ratPoint S'.R (g ≫ α ≫ ρ'.P.A.hom)).unique (by rw [Category.assoc, hα.1.w])
        (by simp only [Category.assoc]; rw [← hα.1.w, reassoc_of% m1, ← reassoc_of% hg']))
    have h1 : h = v₁ ≫ d ≫ m'' := hα''.1.hom_ext (by rw [hh', Category.assoc, Category.assoc, m1''])
      ((existsUnique_ratPoint S''.R (h ≫ α'' ≫ ρ''.P.A.hom)).unique (by rw [Category.assoc, hα''.1.w])
        (by simp only [Category.assoc]; rw [← hα''.1.w, reassoc_of% m1'', ← reassoc_of% hh']))
    rw [g1, h1]; simp only [Category.assoc, key]

end GlobalTheory.UPoinc.USpreadU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVectorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (m k : ℕ), S.N = m ^ 2 → 2 ≤ k → k ∣ m → ∀ ν : u.D.toPre.X, (∀ χ : u.D.toPre.X, m • χ ≠ 0 → l.q ν < l.q (ν + m • χ)) → ∃ h ∈ l.yy.ker, k • m • h = 0 ∧ ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀ * Real.exp (-l.q ν) := by
  first | exact @GlobalTheory.UPoinc.ExactWeight.main | exact GlobalTheory.UPoinc.ExactWeight.main | (intros; apply GlobalTheory.UPoinc.ExactWeight.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilComparisonGeneratorAdditiveFirstVariable
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp.AddFst

theorem prod_pair {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B] (f g : A ⟶ B) {T : Over S} (x y : T ⟶ A)
    {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum B ![fst A A ≫ f, snd A A ≫ g] I.down).left) ^
        ((-1 : ℤ) ^ (2 - I.down.card)) =
      h ((x ≫ f) * (y ≫ g)).left * (h (x ≫ f).left)⁻¹ * (h (y ≫ g).left)⁻¹ * h (1 : T ⟶ B).left := by
  have e : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B ![fst A A ≫ f, snd A A ≫ g] I).left =
      (psum B ![x ≫ f, y ≫ g] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) ![fst A A ≫ f, snd A A ≫ g] I).trans
      (congrArg (fun q => psum B q I) (funext fun i => by fin_cases i <;> simp [preHom])))
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum B ![x ≫ f, y ≫ g] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun I => congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e I.down)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum B ![x ≫ f, y ≫ g] ∅ = 1 := rfl
  have p₁ : psum B ![x ≫ f, y ≫ g] {0} = x ≫ f := _root_.mul_one (x ≫ f)
  have p₂ : psum B ![x ≫ f, y ≫ g] {1} = y ≫ g := _root_.mul_one (y ≫ g)
  have p₃ : psum B ![x ≫ f, y ≫ g] {0, 1} = (x ≫ f) * (y ≫ g) := congrArg ((x ≫ f) * ·) (_root_.mul_one (y ≫ g))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_cmp {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) {T : Over S}
    (x y : T ⟶ P₀.A) {U : Type} [CommGroup U] (h : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → U) :
    ∏ i, h ((lift x y).left ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ i) ^ cmpε i =
      (h (((x ≫ f₂) * (y ≫ g₂)).left ≫ coprod.inr) * (h ((x ≫ f₂).left ≫ coprod.inr))⁻¹ *
          (h ((y ≫ g₂).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ P₂.A).left ≫ coprod.inr)) *
        (h (((x ≫ f₁) * (y ≫ g₁)).left ≫ coprod.inl) * (h ((x ≫ f₁).left ≫ coprod.inl))⁻¹ *
          (h ((y ≫ g₁).left ≫ coprod.inl))⁻¹ * h ((1 : T ⟶ P₁.A).left ≫ coprod.inl))⁻¹ := by
  refine DVR.prod_sum₂ _ ?_ ?_
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (prod_pair f₂ g₂ x y fun q => h (q ≫ coprod.inr))
    rw [Category.assoc]; rfl
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (DVR.prod_neg _ _ (prod_pair f₁ g₁ x y fun q => h (q ≫ coprod.inl)))
    rw [Category.assoc]; rfl

theorem cmp_add_fst : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x x' y : T ⟶ P₀.A), val u (lift (x * x') y).left z J * cubV c₁ z (rl J) (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (val u (lift x y).left z J * val u (lift x' y).left z J) := by
  intro hG S P₀ P₁ P₂ _ _ f₁ g₁ f₂ g₂ _ _ _ _ r₁ hr₁ c₁ r₂ hr₂ c₂ u hu h₀ T z J hJ x x' y
  have hA := P₀.isAb
  let p₀ := x3 P₀.A 0
  let p₁ := x3 P₀.A 1
  let p₂ := x3 P₀.A 2
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J → ∀ a b : T ⟶ P₀.A,
      val (LB.pullGen (join P₁.L P₂.L) _ _ u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J :=
    fun ρ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  have v1 : ∀ {y : (𝟙_ (Over S)).left} {J}, Good (join P₁.L P₂.L) y J →
      val u (lift (1 : 𝟙_ (Over S) ⟶ P₀.A) (1 : 𝟙_ (Over S) ⟶ P₀.A)).left y J = 1 := fun {y J} hJ => by
    have e : lift (1 : 𝟙_ (Over S) ⟶ P₀.A) (1 : 𝟙_ (Over S) ⟶ P₀.A) = lift η[P₀.A] η[P₀.A] := by simp [Hom.one_def]
    have := h₀ _ (𝟙 S) y J hJ
    rw [e]
    exact (congrArg (fun q => val u q y J) (Category.id_comp _)).symm.trans this
  let e : 𝟙_ (Over S) ⟶ G3 P₀.A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have sj : Function.Surjective ((snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  let ρ : T ⟶ G3 P₀.A := lift x (lift x' y)
  have s₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have s₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have s₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have o₂ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [s₀, s₁])
  have hl := isPart_inl P₁.L P₂.L
  have hr := isPart_inr P₁.L P₂.L
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (LB.pullGen (join P₁.L P₂.L) _ _ u (lift (p₀ * p₁) p₂).left)
        (hl.gen (LB.pullGen P₁.L (thφ P₁.A (x3 P₁.A)) thε c₁.t
          (lift (p₀ ≫ f₁) (lift (p₁ ≫ f₁) (p₂ ≫ g₁))).left))) σ.left z J =
        val u (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J *
          cubV c₁ z (rl J) (σ ≫ p₀ ≫ f₁) (σ ≫ p₁ ≫ f₁) (σ ≫ p₂ ≫ g₁) ∧
      val (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (hr.gen (LB.pullGen P₂.L (thφ P₂.A (x3 P₂.A)) thε c₂.t
          (lift (p₀ ≫ f₂) (lift (p₁ ≫ f₂) (p₂ ≫ g₂))).left))
        (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (LB.pullGen (join P₁.L P₂.L) _ _ u (lift p₀ p₂).left)
          (LB.pullGen (join P₁.L P₂.L) _ _ u (lift p₁ p₂).left))) σ.left z J =
        cubV c₂ z (rr J) (σ ≫ p₀ ≫ f₂) (σ ≫ p₁ ≫ f₂) (σ ≫ p₂ ≫ g₂) *
          (val u (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val u (lift (σ ≫ p₁) (σ ≫ p₂)).left z J) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
        ((hl.val_gen _ _ _ hJ).trans (val_cub c₁ σ (hl.good hJ) _ _ _))),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((hr.val_gen _ _ _ hJ).trans (val_cub c₂ σ (hr.good hJ) _ _ _))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
  have key := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' (join_isLB P₁.isLB P₂.isLB) (fun V _ k => ?_) _ e.left he sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (hl.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₁.isGen _)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hr.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₂.isGen _)) (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
  · simp only [← Category.assoc] at key
    rwa [o₂, s₀, s₁, s₂] at key
  · refine (DVR.prod_sum₂ (K := thK) (K' := KK ⊕ KK) (U := V) _
        (prod_cub (p₀ ≫ f₂) (p₁ ≫ f₂) (p₂ ≫ g₂) fun q => k (q ≫ coprod.inr))
        (DVR.prod_sum₂ (K := KK) (K' := KK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₂ k)
          (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₁ p₂ k))).trans
        (Eq.trans ?_ (DVR.prod_sum₂ (K := KK) (K' := thK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ (p₀ * p₁) p₂ k)
          (prod_cub (p₀ ≫ f₁) (p₁ ≫ f₁) (p₂ ≫ g₁) fun q => k (q ≫ coprod.inl))).symm)
    rw [MonObj.mul_comp p₀ p₁ f₁, MonObj.mul_comp p₀ p₁ f₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C₁ := isCub_cubV c₁ (hl.good hI)
    have C₂ := isCub_cubV c₂ (hr.good hI)
    refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
    rw [← Category.assoc e p₀, ← Category.assoc e p₀, o₁, e₀, e₁, e₂, MonObj.one_comp, MonObj.one_comp, v1 hI]
    rw [C₁.face, C₂.face]
    simp

end GlobalTheory.Mum.Two.WeilCmp.AddFst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingTensorTorsionEqProdComponents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem weilQk_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ), 0 < k → ∀ (p' q' : QkPt D'.toPre F k) (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → ∀ z : Fin r → Fin r → Fˣ, (∀ i j, WeilQkIs D.toPre F k (ps i) (qs j) (z i j : F)) → WeilQkIs D'.toPre F k p' q' ((∏ i, ∏ j, z i j ^ (W + W.transpose) i j : Fˣ) : F) := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' k hk p' q' ps qs hp hq z hz
  have gt : BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  have wp : BrWpSt := GlobalTheory.WeilValues.weil_eq_values gt (GlobalTheory.Ex.brFam GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1)
  have hk1 : 1 ≤ k := hk
  have hW := wp R D.toPre D.psi_even D.tau_bimult F N ν k hk1
  have hW' := wp R D'.toPre D'.psi_even D'.tau_bimult F N' ν' k hk1
  have hF := _root_.GlobalTheory.Mum.TensTor.tensFacts_holds R ‹_› D D' W T F N N' ν ν'
  obtain ⟨a', as, ha', has, hra⟩ := hp
  obtain ⟨b', bs, hb', hbs, hrb⟩ := hq
  have hv := _root_.GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hF k hk1 a' b' as bs hra hrb
  refine (hW' p' q' a' b' _ ha' hb').2 ?_
  rw [hv]
  have hz' : ∀ i j, z i j = N.wp (as i) (bs j) := fun i j =>
    Units.ext ((hW (ps i) (qs j) (as i) (bs j) _ (has i) (hbs j)).1 (hz i j))
  simp only [hz']

end GlobalTheory.Mum.TensTor
end

