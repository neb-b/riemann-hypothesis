module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleRestrictScalarsResolutionCompatible
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S)
    (U : Scheme.{0}) (a : Sec F U),
    (GlobalTheory.EtC.restrMap φ F).app U 0 (Sec.map (resι S F) a) =
      Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleRootsOfUnityReductionMapGenerator
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleRootsOfUnityReductionMapGenerator : Prop :=
  ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSchemeGlobalSectionCohomologyClass
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSchemeGlobalSectionCohomologyClass : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k →
    (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 n (by simp) U x = Sec.res x z) ∧
      ∀ (p : ℕ) s h U x, ev (R := R) α.1 (p + 1) s h U x = 0) ∧
    ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n,
      Sec.map (I.d n k) (ev (R := R) α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
      (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X,
        Sec.map (I.d m n) y = ev (R := R) α.1 0 n (by simp) X (𝟙 X))
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiSectionCriteria
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria : Prop :=
  ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafSectionsSeparatedAndGlue
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafShortComplexExactIffLocallyLifts
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts : Prop :=
  ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafificationSectionsLocallyFromPresheaf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf : Prop :=
  ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSimplexSubfaceComposition
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSimplexSubfaceComposition : Prop :=
  ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsFreeDescription
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription : Prop :=
  ∀ (R : Type) [CommRing R] , (∀ E : Spc, ((chains R).obj E).IsStrictlyLE 0) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (p : ℕ), ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom = (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p)))) ∧ ∀ (E : Spc) (p : ℕ), (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsLocallyGenerated
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistSheafFlat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistSingletonTensorGenMul
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTateTwistSingletonTensorGenMul : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ)
end

